%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:33 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 (1469 expanded)
%              Number of clauses        :   89 ( 711 expanded)
%              Number of leaves         :   10 ( 360 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 (2974 expanded)
%              Number of equality atoms :   96 (1097 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t22_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t22_pre_topc])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k9_subset_1(X14,X15,X16) = k3_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_17,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_19,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15]),
    [final]).

fof(c_0_23,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k7_subset_1(X17,X18,X19) = k9_subset_1(X17,X18,k3_subset_1(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_28,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_29,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_34,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_27]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_38,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30]),
    [final]).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20]),c_0_20]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30]),
    [final]).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_20]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38]),
    [final]).

cnf(c_0_45,plain,
    ( k9_subset_1(X1,X2,k3_subset_1(X1,X1)) = k7_subset_1(X1,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30]),
    [final]).

cnf(c_0_46,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38]),
    [final]).

cnf(c_0_47,plain,
    ( k9_subset_1(X1,X2,k3_subset_1(X1,X1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27]),
    [final]).

cnf(c_0_50,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_40]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_30]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(esk2_0,X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_56,plain,
    ( k9_subset_1(X1,k3_subset_1(X2,X2),X1) = k9_subset_1(X2,X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)) = k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1) = k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_48]),
    [final]).

cnf(c_0_60,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1))) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_39]),
    [final]).

cnf(c_0_61,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_22]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_51]),c_0_39]),c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_64,plain,
    ( k9_subset_1(X1,X1,k3_subset_1(X1,X1)) = k7_subset_1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_38])).

cnf(c_0_67,plain,
    ( k9_subset_1(X1,X2,X1) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_46]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,k3_subset_1(X1,X1)) = k9_subset_1(X1,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_53]),
    [final]).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_70,plain,
    ( k9_subset_1(X1,X2,k3_subset_1(X1,X1)) = k1_setfam_1(k2_tarski(k3_subset_1(X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_72,negated_conjecture,
    ( k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(X1,X1)) = k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(X1,X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_57]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_77,negated_conjecture,
    ( k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59]),
    [final]).

cnf(c_0_78,plain,
    ( k9_subset_1(X1,k3_subset_1(X1,X1),X1) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_79,plain,
    ( k9_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_47]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_59]),c_0_63]),
    [final]).

cnf(c_0_81,plain,
    ( k7_subset_1(X1,X1,X1) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_64]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_48]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(esk2_0,u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( k9_subset_1(esk2_0,u1_struct_0(esk1_0),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k9_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_86,plain,
    ( k9_subset_1(X1,X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_61,c_0_38]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_37])).

cnf(c_0_88,plain,
    ( k3_subset_1(X1,X1) = X1
    | ~ r1_tarski(X1,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_50]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = u1_struct_0(esk1_0)
    | ~ r1_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_51]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_42]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_92,plain,
    ( k9_subset_1(X1,k3_subset_1(X2,X2),k3_subset_1(X1,X1)) = k9_subset_1(X2,k3_subset_1(X1,X1),k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_70]),
    [final]).

cnf(c_0_93,plain,
    ( k9_subset_1(X1,k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)),k3_subset_1(X1,X1)) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_70]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_75]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_57]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77]),
    [final]).

cnf(c_0_98,plain,
    ( k9_subset_1(k3_subset_1(X1,X1),X2,k3_subset_1(X1,X1)) = k9_subset_1(X1,X2,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47]),
    [final]).

cnf(c_0_99,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_40]),c_0_78]),
    [final]).

cnf(c_0_100,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),X1) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_79]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_80]),
    [final]).

cnf(c_0_102,plain,
    ( k9_subset_1(X1,X1,k3_subset_1(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_81]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_82]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_35]),c_0_62]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_84]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_66]),
    [final]).

cnf(c_0_107,plain,
    ( k7_subset_1(X1,X1,k3_subset_1(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_30]),c_0_86]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_87]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S089A
% 0.19/0.38  # and selection function SelectCQPrecW.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t22_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.19/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.19/0.38  fof(c_0_10, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2))), inference(assume_negation,[status(cth)],[t22_pre_topc])).
% 0.19/0.38  fof(c_0_12, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|k9_subset_1(X14,X15,X16)=k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.38  fof(c_0_13, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_16, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.38  fof(c_0_17, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.38  fof(c_0_18, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.38  cnf(c_0_19, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15]), ['final']).
% 0.19/0.38  fof(c_0_23, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.38  fof(c_0_24, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.38  fof(c_0_25, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|(~m1_subset_1(X19,k1_zfmisc_1(X17))|k7_subset_1(X17,X18,X19)=k9_subset_1(X17,X18,k3_subset_1(X17,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 0.19/0.38  cnf(c_0_26, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_28, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_29, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.38  cnf(c_0_34, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_28, c_0_27]), ['final']).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk2_0))=k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.19/0.38  cnf(c_0_38, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30]), ['final']).
% 0.19/0.38  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20]), c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_30]), ['final']).
% 0.19/0.38  cnf(c_0_41, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_33, c_0_27]), ['final']).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k9_subset_1(esk2_0,X1,esk2_0)), inference(rw,[status(thm)],[c_0_37, c_0_38]), ['final']).
% 0.19/0.38  cnf(c_0_45, plain, (k9_subset_1(X1,X2,k3_subset_1(X1,X1))=k7_subset_1(X1,X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_30]), ['final']).
% 0.19/0.38  cnf(c_0_46, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_39, c_0_38]), ['final']).
% 0.19/0.38  cnf(c_0_47, plain, (k9_subset_1(X1,X2,k3_subset_1(X1,X1))=k1_setfam_1(k2_tarski(X2,k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_40]), ['final']).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_27]), ['final']).
% 0.19/0.38  cnf(c_0_50, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_33, c_0_40]), ['final']).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_33, c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))=esk2_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_53, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_28, c_0_30]), ['final']).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(esk2_0,X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 0.19/0.38  cnf(c_0_56, plain, (k9_subset_1(X1,k3_subset_1(X2,X2),X1)=k9_subset_1(X2,X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47]), ['final']).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1))=k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_27])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k9_subset_1(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)=k9_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_60, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1)))=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_50]), c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_61, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_41, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_51]), c_0_39]), c_0_46])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_30])).
% 0.19/0.38  cnf(c_0_64, plain, (k9_subset_1(X1,X1,k3_subset_1(X1,X1))=k7_subset_1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_30])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_30])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))=esk2_0), inference(rw,[status(thm)],[c_0_52, c_0_38])).
% 0.19/0.38  cnf(c_0_67, plain, (k9_subset_1(X1,X2,X1)=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_46]), ['final']).
% 0.19/0.38  cnf(c_0_68, plain, (k7_subset_1(X1,X2,k3_subset_1(X1,X1))=k9_subset_1(X1,X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_53]), ['final']).
% 0.19/0.38  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_70, plain, (k9_subset_1(X1,X2,k3_subset_1(X1,X1))=k1_setfam_1(k2_tarski(k3_subset_1(X1,X1),X2))), inference(spm,[status(thm)],[c_0_39, c_0_47]), ['final']).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_40])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k9_subset_1(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(X1,X1))=k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(X1,X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_57]), ['final']).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_45, c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (k9_subset_1(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_59]), ['final']).
% 0.19/0.38  cnf(c_0_78, plain, (k9_subset_1(X1,k3_subset_1(X1,X1),X1)=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.19/0.38  cnf(c_0_79, plain, (k9_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_61, c_0_47]), ['final']).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_59]), c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_81, plain, (k7_subset_1(X1,X1,X1)=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_47]), c_0_64]), ['final']).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(esk2_0,u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_65, c_0_44])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k9_subset_1(esk2_0,u1_struct_0(esk1_0),esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_66, c_0_67]), ['final']).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k9_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_68, c_0_27])).
% 0.19/0.38  cnf(c_0_86, plain, (k9_subset_1(X1,X1,X1)=X1), inference(spm,[status(thm)],[c_0_61, c_0_38]), ['final']).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_61, c_0_37])).
% 0.19/0.38  cnf(c_0_88, plain, (k3_subset_1(X1,X1)=X1|~r1_tarski(X1,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_69, c_0_50]), ['final']).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),esk2_0)=u1_struct_0(esk1_0)|~r1_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_69, c_0_51]), ['final']).
% 0.19/0.38  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_69, c_0_42]), ['final']).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_92, plain, (k9_subset_1(X1,k3_subset_1(X2,X2),k3_subset_1(X1,X1))=k9_subset_1(X2,k3_subset_1(X1,X1),k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_47, c_0_70]), ['final']).
% 0.19/0.38  cnf(c_0_93, plain, (k9_subset_1(X1,k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)),k3_subset_1(X1,X1))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_60, c_0_70]), ['final']).
% 0.19/0.38  cnf(c_0_94, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_71, c_0_72]), ['final']).
% 0.19/0.38  cnf(c_0_95, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_75]), ['final']).
% 0.19/0.38  cnf(c_0_96, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_57]), ['final']).
% 0.19/0.38  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_76, c_0_77]), ['final']).
% 0.19/0.38  cnf(c_0_98, plain, (k9_subset_1(k3_subset_1(X1,X1),X2,k3_subset_1(X1,X1))=k9_subset_1(X1,X2,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_38, c_0_47]), ['final']).
% 0.19/0.38  cnf(c_0_99, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_40]), c_0_78]), ['final']).
% 0.19/0.38  cnf(c_0_100, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),X1)=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_79]), ['final']).
% 0.19/0.38  cnf(c_0_101, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_63, c_0_80]), ['final']).
% 0.19/0.38  cnf(c_0_102, plain, (k9_subset_1(X1,X1,k3_subset_1(X1,X1))=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_64, c_0_81]), ['final']).
% 0.19/0.38  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_82]), ['final']).
% 0.19/0.38  cnf(c_0_104, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_35]), c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_105, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_83, c_0_84]), ['final']).
% 0.19/0.38  cnf(c_0_106, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=esk2_0), inference(rw,[status(thm)],[c_0_85, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_107, plain, (k7_subset_1(X1,X1,k3_subset_1(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_30]), c_0_86]), ['final']).
% 0.19/0.38  cnf(c_0_108, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_87]), ['final']).
% 0.19/0.38  cnf(c_0_109, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 110
% 0.19/0.38  # Proof object clause steps            : 89
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 50
% 0.19/0.38  # Proof object clause conjectures      : 47
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 14
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 56
% 0.19/0.38  # Proof object simplifying inferences  : 34
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 132
% 0.19/0.38  # ...of these trivial                  : 4
% 0.19/0.38  # ...subsumed                          : 29
% 0.19/0.38  # ...remaining for further processing  : 99
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 17
% 0.19/0.38  # Generated clauses                    : 145
% 0.19/0.38  # ...of the previous two non-trivial   : 111
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 143
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 67
% 0.19/0.38  #    Positive orientable unit clauses  : 41
% 0.19/0.38  #    Positive unorientable unit clauses: 10
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 15
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 31
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 19
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 18
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 137
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 312
% 0.19/0.38  # BW rewrite match successes           : 76
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3121
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
