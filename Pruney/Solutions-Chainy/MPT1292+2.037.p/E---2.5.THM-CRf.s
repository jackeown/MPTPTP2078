%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  59 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 140 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_setfam_1(esk2_0,u1_struct_0(esk1_0))
    & esk2_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ( ~ m1_setfam_1(X16,X15)
        | k5_setfam_1(X15,X16) = X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( k5_setfam_1(X15,X16) != X15
        | m1_setfam_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_12,negated_conjecture,
    ( m1_setfam_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | k5_setfam_1(X8,X9) = k3_tarski(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_16,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_21,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_22,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6)))
      | m1_subset_1(k5_setfam_1(X6,X7),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_24,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_18])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k5_setfam_1(X1,k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_18])])).

fof(c_0_29,plain,(
    ! [X17] :
      ( v2_struct_0(X17)
      | ~ l1_struct_0(X17)
      | ~ v1_xboole_0(u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t5_tops_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 0.19/0.37  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.19/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.37  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.19/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.19/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t5_tops_2])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_struct_0(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_setfam_1(esk2_0,u1_struct_0(esk1_0))&esk2_0=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X15, X16]:((~m1_setfam_1(X16,X15)|k5_setfam_1(X15,X16)=X15|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(k5_setfam_1(X15,X16)!=X15|m1_setfam_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (m1_setfam_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (esk2_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_14, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.37  fof(c_0_15, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))|k5_setfam_1(X8,X9)=k3_tarski(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.19/0.37  cnf(c_0_16, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_setfam_1(k1_xboole_0,u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  cnf(c_0_18, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_19, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),k1_xboole_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.19/0.37  fof(c_0_21, plain, ![X4]:(~r1_tarski(X4,k1_xboole_0)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.37  fof(c_0_22, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  fof(c_0_23, plain, ![X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6)))|m1_subset_1(k5_setfam_1(X6,X7),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k3_tarski(k1_xboole_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_18])])).
% 0.19/0.37  cnf(c_0_25, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_27, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k5_setfam_1(X1,k1_xboole_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_18])])).
% 0.19/0.37  fof(c_0_29, plain, ![X17]:(v2_struct_0(X17)|~l1_struct_0(X17)|~v1_xboole_0(u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.37  cnf(c_0_30, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_18])])).
% 0.19/0.37  cnf(c_0_32, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_35, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 38
% 0.19/0.37  # Proof object clause steps            : 20
% 0.19/0.37  # Proof object formula steps           : 18
% 0.19/0.37  # Proof object conjectures             : 14
% 0.19/0.37  # Proof object clause conjectures      : 11
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 9
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 40
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 40
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 7
% 0.19/0.37  # Generated clauses                    : 28
% 0.19/0.37  # ...of the previous two non-trivial   : 25
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 28
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 18
% 0.19/0.37  #    Positive orientable unit clauses  : 5
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 12
% 0.19/0.37  # Current number of unprocessed clauses: 13
% 0.19/0.37  # ...number of literals in the above   : 39
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 22
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 8
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 8
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 4
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1407
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
