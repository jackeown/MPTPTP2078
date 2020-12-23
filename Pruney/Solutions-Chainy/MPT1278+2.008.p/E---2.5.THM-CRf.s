%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  53 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  101 ( 267 expanded)
%              Number of equality atoms :   13 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tops_1(X2,X1) )
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(t86_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(cc4_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v2_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
                & v3_tops_1(X2,X1) )
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_tops_1])).

fof(c_0_5,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_tops_1(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r1_tarski(X10,X9)
        | ~ v3_pre_topc(X10,X8)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_tops_1(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( r1_tarski(esk1_2(X8,X9),X9)
        | v2_tops_1(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(esk1_2(X8,X9),X8)
        | v2_tops_1(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( esk1_2(X8,X9) != k1_xboole_0
        | v2_tops_1(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_tops_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v3_pre_topc(esk3_0,esk2_0)
    & v3_tops_1(esk3_0,esk2_0)
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v3_tops_1(X7,X6)
      | v2_tops_1(X7,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_tops_1])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_9,plain,
    ( X3 = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ v3_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( v2_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v3_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_tops_1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_16]),c_0_12]),c_0_13])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:46:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t97_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tops_1(X2,X1))=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 0.12/0.37  fof(t86_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 0.12/0.37  fof(cc4_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v2_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_tops_1)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tops_1(X2,X1))=>X2=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t97_tops_1])).
% 0.12/0.37  fof(c_0_5, plain, ![X8, X9, X10]:((~v2_tops_1(X9,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|(~r1_tarski(X10,X9)|~v3_pre_topc(X10,X8)|X10=k1_xboole_0))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((m1_subset_1(esk1_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))|v2_tops_1(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(((r1_tarski(esk1_2(X8,X9),X9)|v2_tops_1(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(v3_pre_topc(esk1_2(X8,X9),X8)|v2_tops_1(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8))))&(esk1_2(X8,X9)!=k1_xboole_0|v2_tops_1(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_tops_1])])])])])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((v3_pre_topc(esk3_0,esk2_0)&v3_tops_1(esk3_0,esk2_0))&esk3_0!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X6, X7]:(~v2_pre_topc(X6)|~l1_pre_topc(X6)|(~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|(~v3_tops_1(X7,X6)|v2_tops_1(X7,X6)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_tops_1])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  cnf(c_0_9, plain, (X3=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~v3_pre_topc(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_15, plain, (v2_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tops_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (v3_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (~v2_tops_1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_10]), c_0_16]), c_0_12]), c_0_13])])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_10]), c_0_20])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 22
% 0.12/0.37  # Proof object clause steps            : 13
% 0.12/0.37  # Proof object formula steps           : 9
% 0.12/0.37  # Proof object conjectures             : 12
% 0.12/0.37  # Proof object clause conjectures      : 9
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 4
% 0.12/0.37  # Proof object generating inferences   : 3
% 0.12/0.37  # Proof object simplifying inferences  : 13
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 4
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 15
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 19
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 18
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 8
% 0.12/0.37  # ...of the previous two non-trivial   : 7
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 6
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 16
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 8
% 0.12/0.37  # Current number of unprocessed clauses: 3
% 0.12/0.37  # ...number of literals in the above   : 6
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 0
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 12
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 4
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1197
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
