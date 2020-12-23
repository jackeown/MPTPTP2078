%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   21 ( 111 expanded)
%              Number of clauses        :   16 (  35 expanded)
%              Number of leaves         :    2 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 724 expanded)
%              Number of equality atoms :   11 (  90 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v3_tex_2(X3,X1)
                <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => ( v3_tex_2(X3,X1)
                  <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_tex_2])).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v4_tex_2(X5,X4)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
        | X6 != u1_struct_0(X5)
        | v3_tex_2(X6,X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))
        | v4_tex_2(X5,X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4) )
      & ( esk1_2(X4,X5) = u1_struct_0(X5)
        | v4_tex_2(X5,X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ v3_tex_2(esk1_2(X4,X5),X4)
        | v4_tex_2(X5,X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

fof(c_0_4,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk4_0 = u1_struct_0(esk3_0)
    & ( ~ v3_tex_2(esk4_0,esk2_0)
      | ~ v4_tex_2(esk3_0,esk2_0) )
    & ( v3_tex_2(esk4_0,esk2_0)
      | v4_tex_2(esk3_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( esk4_0 = u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v3_tex_2(X1,X2)
    | v2_struct_0(X2)
    | X1 != esk4_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_tex_2(esk3_0,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_12,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk1_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( esk1_2(esk2_0,esk3_0) = esk4_0
    | v4_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_6]),c_0_9])]),c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v3_tex_2(esk4_0,esk2_0)
    | v4_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( v3_tex_2(esk4_0,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tex_2(esk3_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v4_tex_2(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8]),c_0_9])]),c_0_10]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk2_0)
    | ~ v4_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( v3_tex_2(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16])]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:20:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.18/0.36  # and selection function SelectNewComplexAHP.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t51_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v3_tex_2(X3,X1)<=>v4_tex_2(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_tex_2)).
% 0.18/0.36  fof(d8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v4_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_tex_2(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 0.18/0.36  fof(c_0_2, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v3_tex_2(X3,X1)<=>v4_tex_2(X2,X1))))))), inference(assume_negation,[status(cth)],[t51_tex_2])).
% 0.18/0.36  fof(c_0_3, plain, ![X4, X5, X6]:((~v4_tex_2(X5,X4)|(~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))|(X6!=u1_struct_0(X5)|v3_tex_2(X6,X4)))|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~l1_pre_topc(X4)))&((m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))|v4_tex_2(X5,X4)|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~l1_pre_topc(X4)))&((esk1_2(X4,X5)=u1_struct_0(X5)|v4_tex_2(X5,X4)|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~l1_pre_topc(X4)))&(~v3_tex_2(esk1_2(X4,X5),X4)|v4_tex_2(X5,X4)|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~l1_pre_topc(X4)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).
% 0.18/0.36  fof(c_0_4, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_pre_topc(esk3_0,esk2_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(esk4_0=u1_struct_0(esk3_0)&((~v3_tex_2(esk4_0,esk2_0)|~v4_tex_2(esk3_0,esk2_0))&(v3_tex_2(esk4_0,esk2_0)|v4_tex_2(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).
% 0.18/0.36  cnf(c_0_5, plain, (v3_tex_2(X3,X2)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.18/0.36  cnf(c_0_6, negated_conjecture, (esk4_0=u1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_7, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v4_tex_2(X2,X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.18/0.36  cnf(c_0_8, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_9, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_10, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_11, negated_conjecture, (v3_tex_2(X1,X2)|v2_struct_0(X2)|X1!=esk4_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_tex_2(esk3_0,X2)|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.18/0.36  cnf(c_0_12, plain, (v4_tex_2(X2,X1)|v2_struct_0(X1)|~v3_tex_2(esk1_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (esk1_2(esk2_0,esk3_0)=esk4_0|v4_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_6]), c_0_9])]), c_0_10])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (v3_tex_2(esk4_0,esk2_0)|v4_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (v3_tex_2(esk4_0,X1)|v2_struct_0(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))|~v4_tex_2(esk3_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (v4_tex_2(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_8]), c_0_9])]), c_0_10]), c_0_14])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (~v3_tex_2(esk4_0,esk2_0)|~v4_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (v3_tex_2(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_8]), c_0_9])]), c_0_10])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16])]), c_0_19])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 21
% 0.18/0.36  # Proof object clause steps            : 16
% 0.18/0.36  # Proof object formula steps           : 5
% 0.18/0.36  # Proof object conjectures             : 16
% 0.18/0.36  # Proof object clause conjectures      : 13
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 10
% 0.18/0.36  # Proof object initial formulas used   : 2
% 0.18/0.36  # Proof object generating inferences   : 5
% 0.18/0.36  # Proof object simplifying inferences  : 18
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 2
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 11
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 11
% 0.18/0.36  # Processed clauses                    : 21
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 1
% 0.18/0.36  # ...remaining for further processing  : 18
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 3
% 0.18/0.36  # Generated clauses                    : 10
% 0.18/0.36  # ...of the previous two non-trivial   : 10
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 8
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 2
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 15
% 0.18/0.36  #    Positive orientable unit clauses  : 6
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 8
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 3
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 9
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 2
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.36  # Unit Clause-clause subsumption calls : 0
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 1
% 0.18/0.36  # BW rewrite match successes           : 1
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 1038
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.027 s
% 0.18/0.37  # System time              : 0.004 s
% 0.18/0.37  # Total time               : 0.030 s
% 0.18/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
