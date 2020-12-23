%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:02 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  62 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   85 ( 207 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t29_pre_topc])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] :
      ( ( X6 != k1_pre_topc(X4,X5)
        | k2_struct_0(X6) = X5
        | ~ v1_pre_topc(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( k2_struct_0(X6) != X5
        | X6 = k1_pre_topc(X4,X5)
        | ~ v1_pre_topc(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_7,plain,(
    ! [X7,X8] :
      ( ( v1_pre_topc(k1_pre_topc(X7,X8))
        | ~ l1_pre_topc(X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) )
      & ( m1_pre_topc(k1_pre_topc(X7,X8),X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & u1_struct_0(k1_pre_topc(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_15,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10]),c_0_11]),
    [final]).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_13]),c_0_14])]),
    [final]).

cnf(c_0_20,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1_0,esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14])]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_13]),c_0_14])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:30:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.35  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.027 s
% 0.18/0.35  # Presaturation interreduction done
% 0.18/0.35  
% 0.18/0.35  # No proof found!
% 0.18/0.35  # SZS status CounterSatisfiable
% 0.18/0.35  # SZS output start Saturation
% 0.18/0.35  fof(t29_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.18/0.35  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.18/0.35  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.18/0.35  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.35  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.35  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2))), inference(assume_negation,[status(cth)],[t29_pre_topc])).
% 0.18/0.35  fof(c_0_6, plain, ![X4, X5, X6]:((X6!=k1_pre_topc(X4,X5)|k2_struct_0(X6)=X5|(~v1_pre_topc(X6)|~m1_pre_topc(X6,X4))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(k2_struct_0(X6)!=X5|X6=k1_pre_topc(X4,X5)|(~v1_pre_topc(X6)|~m1_pre_topc(X6,X4))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.18/0.35  fof(c_0_7, plain, ![X7, X8]:((v1_pre_topc(k1_pre_topc(X7,X8))|(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))))&(m1_pre_topc(k1_pre_topc(X7,X8),X7)|(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.18/0.35  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&u1_struct_0(k1_pre_topc(esk1_0,esk2_0))!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.18/0.35  cnf(c_0_9, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.35  cnf(c_0_10, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.18/0.35  cnf(c_0_11, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.18/0.35  fof(c_0_12, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.35  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.35  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.35  cnf(c_0_15, plain, (X1=k1_pre_topc(X3,X2)|k2_struct_0(X1)!=X2|~v1_pre_topc(X1)|~m1_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.35  fof(c_0_16, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.36  cnf(c_0_17, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10]), c_0_11]), ['final']).
% 0.18/0.36  cnf(c_0_18, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_13]), c_0_14])]), ['final']).
% 0.18/0.36  cnf(c_0_20, plain, (k1_pre_topc(X1,k2_struct_0(X2))=X2|~m1_pre_topc(X2,X1)|~v1_pre_topc(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_21, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (u1_struct_0(k1_pre_topc(esk1_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (k2_struct_0(k1_pre_topc(esk1_0,esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14])]), ['final']).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_14])]), ['final']).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (v1_pre_topc(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_13]), c_0_14])]), ['final']).
% 0.18/0.36  # SZS output end Saturation
% 0.18/0.36  # Proof object total steps             : 26
% 0.18/0.36  # Proof object clause steps            : 15
% 0.18/0.36  # Proof object formula steps           : 11
% 0.18/0.36  # Proof object conjectures             : 10
% 0.18/0.36  # Proof object clause conjectures      : 7
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 9
% 0.18/0.36  # Proof object initial formulas used   : 5
% 0.18/0.36  # Proof object generating inferences   : 4
% 0.18/0.36  # Proof object simplifying inferences  : 12
% 0.18/0.36  # Parsed axioms                        : 5
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 9
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 9
% 0.18/0.36  # Processed clauses                    : 25
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 25
% 0.18/0.36  # Other redundant clauses eliminated   : 2
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 1
% 0.18/0.36  # Generated clauses                    : 7
% 0.18/0.36  # ...of the previous two non-trivial   : 7
% 0.18/0.36  # Contextual simplify-reflections      : 2
% 0.18/0.36  # Paramodulations                      : 5
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
% 0.18/0.36  # Current number of processed clauses  : 13
% 0.18/0.36  #    Positive orientable unit clauses  : 6
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 6
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 10
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 54
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 20
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.36  # Unit Clause-clause subsumption calls : 0
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 1
% 0.18/0.36  # BW rewrite match successes           : 1
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 851
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.028 s
% 0.18/0.36  # System time              : 0.003 s
% 0.18/0.36  # Total time               : 0.032 s
% 0.18/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
