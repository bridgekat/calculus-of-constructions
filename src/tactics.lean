import init.meta.tactic
import tactic.interactive

namespace tactic.interactive

open tactic
open interactive

/-- Unmodified core implementation. -/
private meta def goals_with_matching_tag (ns : list name) : tactic (list (expr × case_tag) × list (expr × case_tag)) := do
  gs ← get_goals,
  (gs : list (expr × tag)) ← gs.mmap (λ g, do t ← get_tag g, pure (g, t)),
  pure $ gs.foldr
    (λ ⟨g, t⟩ ⟨exact_matches, suffix_matches⟩,
      match case_tag.parse t with
      | none := ⟨exact_matches, suffix_matches⟩
      | some t :=
        match case_tag.match_tag ns t with
        | case_tag.match_result.exact_match := ⟨⟨g, t⟩ :: exact_matches, suffix_matches⟩
        | case_tag.match_result.fuzzy_match := ⟨exact_matches, ⟨g, t⟩ :: suffix_matches⟩
        | case_tag.match_result.no_match    := ⟨exact_matches, suffix_matches⟩
        end
      end)
    ([], [])

/-- Modified core implementation to allow multiple goals with the given suffix
    (in which case it chooses the first one). -/
private meta def goal_with_matching_tag (ns : list name) : tactic (expr × case_tag) := do
  ⟨exact_matches, suffix_matches⟩ ← goals_with_matching_tag ns,
  match exact_matches, suffix_matches with
  | [],        []        := fail format! "Invalid `case`: there is no goal tagged with suffix {ns}."
  | [],        (g :: gs) := pure g
  | (g :: gs), _         := pure g
  end

/-- Unmodified core implementation. -/
meta def case' (args : parse case_parser) (tac : itactic) : tactic unit := do
  target_goals ← args.mmap (λ ⟨ns, ids⟩, do
    ⟨goal, tag⟩ ← goal_with_matching_tag ns,
    let ids := ids.get_or_else [],
    let num_ids := ids.length,
    goals ← get_goals,
    let other_goals := goals.filter (≠ goal),
    set_goals [goal],
    match tag with
    | (case_tag.pi _ num_args) := do
      intro_lst ids,
      when (num_ids < num_args) $ intron (num_args - num_ids)
    | (case_tag.hyps _ new_hyp_names) := do
        let num_new_hyps := new_hyp_names.length,
        when (num_ids > num_new_hyps) $ fail format!
          ("Invalid `case`: You gave {num_ids} names, but the case introduces " ++
          "{num_new_hyps} new hypotheses."),
        let renamings := native.rb_map.of_list (new_hyp_names.zip ids),
        propagate_tags $ tactic.rename_many renamings tt tt
    end,
    goals ← get_goals,
    set_goals other_goals,
    match goals with
    | [g] := return g
    | _ := fail "Unexpected goals introduced by renaming"
    end),
  remaining_goals ← get_goals,
  set_goals target_goals,
  tac,
  unsolved_goals ← get_goals,
  match unsolved_goals with
  | [] := set_goals remaining_goals
  | _  := fail "`case` tactic failed, focused goals have not been solved"
  end

end tactic.interactive
