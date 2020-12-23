%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:50 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  65 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 150 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & m1_setfam_1(esk3_0,u1_struct_0(esk2_0))
    & esk3_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ( ~ m1_setfam_1(X17,X16)
        | k5_setfam_1(X16,X17) = X16
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( k5_setfam_1(X16,X17) != X16
        | m1_setfam_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_13,negated_conjecture,
    ( m1_setfam_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | k5_setfam_1(X9,X10) = k3_tarski(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | ~ r1_tarski(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk2_0),k1_xboole_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X4] :
      ( X4 = k1_xboole_0
      | r2_hidden(esk1_1(X4),X4) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))
      | m1_subset_1(k5_setfam_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_29,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_29])).

fof(c_0_34,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_1(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:04:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.35  #
% 0.14/0.35  # Preprocessing time       : 0.014 s
% 0.14/0.35  # Presaturation interreduction done
% 0.14/0.35  
% 0.14/0.35  # Proof found!
% 0.14/0.35  # SZS status Theorem
% 0.14/0.35  # SZS output start CNFRefutation
% 0.14/0.35  fof(t5_tops_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 0.14/0.35  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.14/0.35  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.35  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.14/0.35  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.35  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.35  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.35  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.14/0.35  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.35  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.35  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t5_tops_2])).
% 0.14/0.35  fof(c_0_11, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(m1_setfam_1(esk3_0,u1_struct_0(esk2_0))&esk3_0=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.14/0.35  fof(c_0_12, plain, ![X16, X17]:((~m1_setfam_1(X17,X16)|k5_setfam_1(X16,X17)=X16|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&(k5_setfam_1(X16,X17)!=X16|m1_setfam_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.14/0.35  cnf(c_0_13, negated_conjecture, (m1_setfam_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.35  cnf(c_0_14, negated_conjecture, (esk3_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.35  fof(c_0_15, plain, ![X6]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.35  fof(c_0_16, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))|k5_setfam_1(X9,X10)=k3_tarski(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.14/0.35  cnf(c_0_17, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.35  cnf(c_0_18, negated_conjecture, (m1_setfam_1(k1_xboole_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.35  cnf(c_0_19, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.35  cnf(c_0_20, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.35  fof(c_0_21, plain, ![X18, X19]:(~r2_hidden(X18,X19)|~r1_tarski(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.35  fof(c_0_22, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.35  cnf(c_0_23, negated_conjecture, (k5_setfam_1(u1_struct_0(esk2_0),k1_xboole_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.14/0.35  cnf(c_0_24, plain, (k5_setfam_1(X1,k1_xboole_0)=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.14/0.35  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.35  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.35  fof(c_0_27, plain, ![X4]:(X4=k1_xboole_0|r2_hidden(esk1_1(X4),X4)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.35  fof(c_0_28, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))|m1_subset_1(k5_setfam_1(X7,X8),k1_zfmisc_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.14/0.35  cnf(c_0_29, negated_conjecture, (k3_tarski(k1_xboole_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.35  cnf(c_0_30, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.35  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.35  cnf(c_0_32, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.35  cnf(c_0_33, plain, (k5_setfam_1(X1,k1_xboole_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_24, c_0_29])).
% 0.14/0.35  fof(c_0_34, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.35  cnf(c_0_35, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(esk1_1(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.35  cnf(c_0_36, plain, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19])])).
% 0.14/0.35  cnf(c_0_37, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.35  cnf(c_0_38, plain, (u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.35  cnf(c_0_39, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.35  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.35  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.35  cnf(c_0_42, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])]), c_0_41]), ['proof']).
% 0.14/0.35  # SZS output end CNFRefutation
% 0.14/0.35  # Proof object total steps             : 43
% 0.14/0.35  # Proof object clause steps            : 23
% 0.14/0.35  # Proof object formula steps           : 20
% 0.14/0.35  # Proof object conjectures             : 10
% 0.14/0.35  # Proof object clause conjectures      : 7
% 0.14/0.35  # Proof object formula conjectures     : 3
% 0.14/0.35  # Proof object initial clauses used    : 13
% 0.14/0.35  # Proof object initial formulas used   : 10
% 0.14/0.35  # Proof object generating inferences   : 7
% 0.14/0.35  # Proof object simplifying inferences  : 11
% 0.14/0.35  # Training examples: 0 positive, 0 negative
% 0.14/0.35  # Parsed axioms                        : 11
% 0.14/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.35  # Initial clauses                      : 17
% 0.14/0.35  # Removed in clause preprocessing      : 0
% 0.14/0.35  # Initial clauses in saturation        : 17
% 0.14/0.35  # Processed clauses                    : 45
% 0.14/0.35  # ...of these trivial                  : 0
% 0.14/0.35  # ...subsumed                          : 0
% 0.14/0.35  # ...remaining for further processing  : 45
% 0.14/0.35  # Other redundant clauses eliminated   : 0
% 0.14/0.35  # Clauses deleted for lack of memory   : 0
% 0.14/0.35  # Backward-subsumed                    : 0
% 0.14/0.35  # Backward-rewritten                   : 10
% 0.14/0.35  # Generated clauses                    : 19
% 0.14/0.35  # ...of the previous two non-trivial   : 22
% 0.14/0.35  # Contextual simplify-reflections      : 0
% 0.14/0.35  # Paramodulations                      : 19
% 0.14/0.35  # Factorizations                       : 0
% 0.14/0.35  # Equation resolutions                 : 0
% 0.14/0.35  # Propositional unsat checks           : 0
% 0.14/0.35  #    Propositional check models        : 0
% 0.14/0.35  #    Propositional check unsatisfiable : 0
% 0.14/0.35  #    Propositional clauses             : 0
% 0.14/0.35  #    Propositional clauses after purity: 0
% 0.14/0.35  #    Propositional unsat core size     : 0
% 0.14/0.35  #    Propositional preprocessing time  : 0.000
% 0.14/0.35  #    Propositional encoding time       : 0.000
% 0.14/0.35  #    Propositional solver time         : 0.000
% 0.14/0.35  #    Success case prop preproc time    : 0.000
% 0.14/0.35  #    Success case prop encoding time   : 0.000
% 0.14/0.35  #    Success case prop solver time     : 0.000
% 0.14/0.35  # Current number of processed clauses  : 19
% 0.14/0.35  #    Positive orientable unit clauses  : 5
% 0.14/0.35  #    Positive unorientable unit clauses: 0
% 0.14/0.35  #    Negative unit clauses             : 1
% 0.14/0.35  #    Non-unit-clauses                  : 13
% 0.14/0.35  # Current number of unprocessed clauses: 5
% 0.14/0.35  # ...number of literals in the above   : 9
% 0.14/0.35  # Current number of archived formulas  : 0
% 0.14/0.35  # Current number of archived clauses   : 26
% 0.14/0.35  # Clause-clause subsumption calls (NU) : 22
% 0.14/0.35  # Rec. Clause-clause subsumption calls : 22
% 0.14/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.35  # Unit Clause-clause subsumption calls : 1
% 0.14/0.35  # Rewrite failures with RHS unbound    : 4
% 0.14/0.35  # BW rewrite match attempts            : 5
% 0.14/0.35  # BW rewrite match successes           : 5
% 0.14/0.35  # Condensation attempts                : 0
% 0.14/0.35  # Condensation successes               : 0
% 0.14/0.35  # Termbank termtop insertions          : 1375
% 0.14/0.35  
% 0.14/0.35  # -------------------------------------------------
% 0.14/0.35  # User time                : 0.012 s
% 0.14/0.35  # System time              : 0.006 s
% 0.14/0.35  # Total time               : 0.018 s
% 0.14/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
