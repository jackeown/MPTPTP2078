%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:52 EST 2020

% Result     : CounterSatisfiable 0.11s
% Output     : Saturation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 304 expanded)
%              Number of clauses        :   41 ( 134 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 659 expanded)
%              Number of equality atoms :   56 ( 339 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t25_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                  & r1_xboole_0(X2,X3) )
               => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_12,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | k4_xboole_0(k2_xboole_0(X12,X13),X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X10,X11] : k3_xboole_0(X10,k2_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                    & r1_xboole_0(X2,X3) )
                 => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_pre_topc])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_16]),
    [final]).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_29,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_31,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k4_subset_1(X18,X19,X20) = k2_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2)))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_34,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_19]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_39,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_40,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26]),
    [final]).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( k2_struct_0(esk1_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),
    [final]).

cnf(c_0_44,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X1) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,k2_xboole_0(X2,X3),X2) = k5_xboole_0(k2_xboole_0(X2,X3),X2)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27]),
    [final]).

cnf(c_0_46,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

fof(c_0_48,plain,(
    ! [X17] : m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_49,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_50,plain,
    ( k7_subset_1(X1,k2_xboole_0(X2,X3),X3) = k5_xboole_0(k2_xboole_0(X2,X3),X3)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk2_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_52,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_34]),
    [final]).

cnf(c_0_53,plain,
    ( k7_subset_1(X1,k2_xboole_0(X2,X3),X2) = X3
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47]),
    [final]).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,k2_xboole_0(X2,X3),X3) = X2
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_45]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(X1,k2_xboole_0(esk2_0,esk3_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52]),
    [final]).

cnf(c_0_60,plain,
    ( k7_subset_1(X1,X2,k2_xboole_0(X3,X2)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33]),
    [final]).

cnf(c_0_61,plain,
    ( k7_subset_1(X1,X2,k2_xboole_0(X2,X3)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_54])]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_43]),
    [final]).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:54:23 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.026 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # No proof found!
% 0.11/0.36  # SZS status CounterSatisfiable
% 0.11/0.36  # SZS output start Saturation
% 0.11/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.11/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.11/0.36  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.11/0.36  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.11/0.36  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.11/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.11/0.36  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.11/0.36  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 0.11/0.36  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.11/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.11/0.36  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.11/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.11/0.36  fof(c_0_12, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.11/0.36  fof(c_0_13, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.11/0.36  fof(c_0_14, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|k4_xboole_0(k2_xboole_0(X12,X13),X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.11/0.36  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.36  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.36  fof(c_0_17, plain, ![X10, X11]:k3_xboole_0(X10,k2_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.11/0.36  cnf(c_0_18, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.11/0.36  fof(c_0_20, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.11/0.36  cnf(c_0_21, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.36  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.11/0.36  fof(c_0_23, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k7_subset_1(X21,X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.11/0.36  fof(c_0_24, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 0.11/0.36  cnf(c_0_25, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.36  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.11/0.36  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_21, c_0_16]), ['final']).
% 0.11/0.36  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.11/0.36  cnf(c_0_29, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.36  fof(c_0_30, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.11/0.36  fof(c_0_31, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|~m1_subset_1(X20,k1_zfmisc_1(X18))|k4_subset_1(X18,X19,X20)=k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.11/0.36  cnf(c_0_32, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.11/0.36  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.11/0.36  cnf(c_0_34, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_19]), ['final']).
% 0.11/0.36  cnf(c_0_35, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.36  cnf(c_0_36, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.11/0.36  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.11/0.36  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.11/0.36  cnf(c_0_39, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.11/0.36  cnf(c_0_40, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_26]), ['final']).
% 0.11/0.36  fof(c_0_41, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.11/0.36  cnf(c_0_42, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.36  cnf(c_0_43, negated_conjecture, (k2_struct_0(esk1_0)=k2_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])]), ['final']).
% 0.11/0.36  cnf(c_0_44, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X1)=X2|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_28]), ['final']).
% 0.11/0.36  cnf(c_0_45, plain, (k7_subset_1(X1,k2_xboole_0(X2,X3),X2)=k5_xboole_0(k2_xboole_0(X2,X3),X2)|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_27]), ['final']).
% 0.11/0.36  cnf(c_0_46, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.11/0.36  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.11/0.36  fof(c_0_48, plain, ![X17]:m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.11/0.36  fof(c_0_49, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.11/0.36  cnf(c_0_50, plain, (k7_subset_1(X1,k2_xboole_0(X2,X3),X3)=k5_xboole_0(k2_xboole_0(X2,X3),X3)|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_33]), ['final']).
% 0.11/0.36  cnf(c_0_51, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk2_0)!=esk3_0), inference(rw,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.11/0.36  cnf(c_0_52, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_34, c_0_34]), ['final']).
% 0.11/0.36  cnf(c_0_53, plain, (k7_subset_1(X1,k2_xboole_0(X2,X3),X2)=X3|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45]), ['final']).
% 0.11/0.36  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_47]), ['final']).
% 0.11/0.36  cnf(c_0_55, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.11/0.36  cnf(c_0_56, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.11/0.36  cnf(c_0_57, plain, (k7_subset_1(X1,k2_xboole_0(X2,X3),X3)=X2|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_50]), ['final']).
% 0.11/0.36  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk2_0)!=esk3_0|~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_51, c_0_45]), ['final']).
% 0.11/0.36  cnf(c_0_59, negated_conjecture, (k7_subset_1(X1,k2_xboole_0(esk2_0,esk3_0),esk2_0)!=esk3_0|~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52]), ['final']).
% 0.11/0.36  cnf(c_0_60, plain, (k7_subset_1(X1,X2,k2_xboole_0(X3,X2))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_33]), ['final']).
% 0.11/0.36  cnf(c_0_61, plain, (k7_subset_1(X1,X2,k2_xboole_0(X2,X3))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_27]), ['final']).
% 0.11/0.36  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_53]), c_0_54])]), ['final']).
% 0.11/0.36  cnf(c_0_63, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_35, c_0_43]), ['final']).
% 0.11/0.36  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.11/0.36  cnf(c_0_65, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.11/0.36  # SZS output end Saturation
% 0.11/0.36  # Proof object total steps             : 66
% 0.11/0.36  # Proof object clause steps            : 41
% 0.11/0.36  # Proof object formula steps           : 25
% 0.11/0.36  # Proof object conjectures             : 16
% 0.11/0.36  # Proof object clause conjectures      : 13
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 17
% 0.11/0.36  # Proof object initial formulas used   : 12
% 0.11/0.36  # Proof object generating inferences   : 15
% 0.11/0.36  # Proof object simplifying inferences  : 14
% 0.11/0.36  # Parsed axioms                        : 12
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 17
% 0.11/0.36  # Removed in clause preprocessing      : 3
% 0.11/0.36  # Initial clauses in saturation        : 14
% 0.11/0.36  # Processed clauses                    : 111
% 0.11/0.36  # ...of these trivial                  : 5
% 0.11/0.36  # ...subsumed                          : 60
% 0.11/0.36  # ...remaining for further processing  : 46
% 0.11/0.36  # Other redundant clauses eliminated   : 0
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 1
% 0.11/0.36  # Backward-rewritten                   : 2
% 0.11/0.36  # Generated clauses                    : 94
% 0.11/0.36  # ...of the previous two non-trivial   : 88
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 94
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 0
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 29
% 0.11/0.36  #    Positive orientable unit clauses  : 10
% 0.11/0.36  #    Positive unorientable unit clauses: 2
% 0.11/0.36  #    Negative unit clauses             : 2
% 0.11/0.36  #    Non-unit-clauses                  : 15
% 0.11/0.36  # Current number of unprocessed clauses: 0
% 0.11/0.36  # ...number of literals in the above   : 0
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 20
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 172
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 153
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 61
% 0.11/0.36  # Unit Clause-clause subsumption calls : 2
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 6
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 2068
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.028 s
% 0.11/0.36  # System time              : 0.004 s
% 0.11/0.36  # Total time               : 0.032 s
% 0.11/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
