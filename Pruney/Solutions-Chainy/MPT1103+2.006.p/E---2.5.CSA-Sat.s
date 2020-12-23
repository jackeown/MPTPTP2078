%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:37 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 242 expanded)
%              Number of clauses        :   32 ( 112 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 449 expanded)
%              Number of equality atoms :   65 ( 302 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(c_0_10,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k7_subset_1(X14,X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ~ l1_struct_0(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k7_subset_1(u1_struct_0(X19),k2_struct_0(X19),k7_subset_1(u1_struct_0(X19),k2_struct_0(X19),X20)) = X20 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_20]),
    [final]).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_38,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_43,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_35]),
    [final]).

cnf(c_0_44,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35]),
    [final]).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | k7_subset_1(X1,X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_35]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_37]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_30])]),
    [final]).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_35]),
    [final]).

cnf(c_0_52,plain,
    ( k7_subset_1(X1,X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:32:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.12/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.37  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.12/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.12/0.37  fof(c_0_10, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_12, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k7_subset_1(X14,X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.12/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_15, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.37  fof(c_0_16, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.12/0.37  fof(c_0_18, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.37  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_23, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.12/0.37  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  fof(c_0_25, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_tarski(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.37  fof(c_0_26, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  cnf(c_0_27, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.37  fof(c_0_31, plain, ![X19, X20]:(~l1_struct_0(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k7_subset_1(u1_struct_0(X19),k2_struct_0(X19),k7_subset_1(u1_struct_0(X19),k2_struct_0(X19),X20))=X20)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.12/0.37  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_20]), ['final']).
% 0.12/0.37  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_20])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.12/0.37  cnf(c_0_38, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.12/0.37  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34]), ['final']).
% 0.12/0.37  cnf(c_0_43, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_27, c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_44, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_45, plain, (r1_tarski(X1,X2)|k7_subset_1(X1,X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_37]), ['final']).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_30])]), ['final']).
% 0.12/0.37  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_33]), ['final']).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_37, c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_52, plain, (k7_subset_1(X1,X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_42])]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 53
% 0.12/0.37  # Proof object clause steps            : 32
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 11
% 0.12/0.37  # Proof object clause conjectures      : 8
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 14
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 5
% 0.12/0.37  # Initial clauses in saturation        : 13
% 0.12/0.37  # Processed clauses                    : 52
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 11
% 0.12/0.37  # ...remaining for further processing  : 40
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 6
% 0.12/0.37  # Generated clauses                    : 40
% 0.12/0.37  # ...of the previous two non-trivial   : 29
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 38
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
% 0.12/0.37  # Current number of processed clauses  : 20
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 11
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 21
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 29
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 28
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 11
% 0.12/0.37  # Unit Clause-clause subsumption calls : 5
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 22
% 0.12/0.37  # BW rewrite match successes           : 10
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1413
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
