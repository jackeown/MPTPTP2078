%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:48 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 242 expanded)
%              Number of clauses        :   35 ( 113 expanded)
%              Number of leaves         :   13 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 394 expanded)
%              Number of equality atoms :   69 ( 276 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t23_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k2_struct_0(X1)
                & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                & X2 = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(c_0_13,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k7_subset_1(X17,X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X16] : m1_subset_1(k2_subset_1(X16),k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_19,plain,(
    ! [X15] : k2_subset_1(X15) = X15 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_20,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_21,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k3_xboole_0(X7,X8) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_26,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X10,X11)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24]),
    [final]).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_17]),
    [final]).

fof(c_0_36,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_37,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k7_subset_1(X1,X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_17]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_34]),c_0_34]),
    [final]).

cnf(c_0_46,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [final]).

fof(c_0_47,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X1) = k7_subset_1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42]),
    [final]).

fof(c_0_50,plain,(
    ! [X22,X23] :
      ( ~ l1_struct_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),X23)) = X23 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49]),
    [final]).

cnf(c_0_53,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_52]),
    [final]).

cnf(c_0_58,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_34]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_51])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_34]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.045 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # No proof found!
% 0.13/0.39  # SZS status CounterSatisfiable
% 0.13/0.39  # SZS output start Saturation
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.13/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.39  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.13/0.39  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.39  fof(c_0_13, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_14, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.39  fof(c_0_15, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k7_subset_1(X17,X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.39  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_18, plain, ![X16]:m1_subset_1(k2_subset_1(X16),k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.39  fof(c_0_19, plain, ![X15]:k2_subset_1(X15)=X15, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.39  fof(c_0_20, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.39  cnf(c_0_21, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_25, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k3_xboole_0(X7,X8)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.39  fof(c_0_26, plain, ![X10, X11]:k4_xboole_0(X10,k2_xboole_0(X10,X11))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.13/0.39  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_28, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.39  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_23, c_0_24]), ['final']).
% 0.13/0.39  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_31, plain, ![X4]:k3_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_27, c_0_22])).
% 0.13/0.39  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.13/0.39  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_17]), ['final']).
% 0.13/0.39  fof(c_0_36, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  fof(c_0_37, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.39  cnf(c_0_38, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_39, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_33])).
% 0.13/0.39  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k7_subset_1(X1,X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.39  cnf(c_0_42, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.13/0.39  fof(c_0_43, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.13/0.39  cnf(c_0_44, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_38, c_0_17]), ['final']).
% 0.13/0.39  cnf(c_0_45, plain, (k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_34]), c_0_34]), ['final']).
% 0.13/0.39  cnf(c_0_46, plain, (k7_subset_1(k1_xboole_0,k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['final']).
% 0.13/0.39  fof(c_0_47, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).
% 0.13/0.39  cnf(c_0_48, plain, (k5_xboole_0(X1,X1)=k7_subset_1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.13/0.39  cnf(c_0_49, plain, (k7_subset_1(X1,X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42]), ['final']).
% 0.13/0.39  fof(c_0_50, plain, ![X22, X23]:(~l1_struct_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),X23))=X23)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.39  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49]), ['final']).
% 0.13/0.39  cnf(c_0_53, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_51])).
% 0.13/0.39  cnf(c_0_57, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_52]), ['final']).
% 0.13/0.39  cnf(c_0_58, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_28, c_0_34]), ['final']).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_51])]), ['final']).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_56, c_0_34]), ['final']).
% 0.13/0.39  # SZS output end Saturation
% 0.13/0.39  # Proof object total steps             : 62
% 0.13/0.39  # Proof object clause steps            : 35
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 10
% 0.13/0.39  # Proof object clause conjectures      : 7
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 16
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 7
% 0.13/0.39  # Proof object simplifying inferences  : 19
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 18
% 0.13/0.39  # Removed in clause preprocessing      : 6
% 0.13/0.39  # Initial clauses in saturation        : 12
% 0.13/0.39  # Processed clauses                    : 56
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 5
% 0.13/0.39  # ...remaining for further processing  : 49
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 17
% 0.13/0.39  # Generated clauses                    : 47
% 0.13/0.39  # ...of the previous two non-trivial   : 45
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 47
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 19
% 0.13/0.39  #    Positive orientable unit clauses  : 12
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 7
% 0.13/0.39  # Current number of unprocessed clauses: 0
% 0.13/0.39  # ...number of literals in the above   : 0
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 34
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 49
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 40
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.39  # Unit Clause-clause subsumption calls : 3
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 66
% 0.13/0.39  # BW rewrite match successes           : 16
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1632
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.045 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.052 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
