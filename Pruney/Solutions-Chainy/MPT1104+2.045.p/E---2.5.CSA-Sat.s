%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:55 EST 2020

% Result     : CounterSatisfiable 1.91s
% Output     : Saturation 1.91s
% Verified   : 
% Statistics : Number of formulae       : 1388 (178413 expanded)
%              Number of clauses        : 1363 (86081 expanded)
%              Number of leaves         :   12 (45353 expanded)
%              Depth                    :   36
%              Number of atoms          : 5854 (301321 expanded)
%              Number of equality atoms : 1440 (172621 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(c_0_12,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_19,plain,(
    ! [X14,X15] : k3_tarski(k2_tarski(X14,X15)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_20,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k4_subset_1(X18,X19,X20) = k2_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_27,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_16]),
    [final]).

fof(c_0_30,plain,(
    ! [X17] : m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_31,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_16]),
    [final]).

cnf(c_0_33,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_35,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29]),
    [final]).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_28]),
    [final]).

cnf(c_0_39,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_25]),
    [final]).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37]),
    [final]).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_44,plain,
    ( k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39]),
    [final]).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_42]),
    [final]).

cnf(c_0_47,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_16]),
    [final]).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47]),
    [final]).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_28]),
    [final]).

cnf(c_0_51,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_49]),c_0_28])).

cnf(c_0_52,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28]),
    [final]).

cnf(c_0_53,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32])]),
    [final]).

cnf(c_0_54,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41]),
    [final]).

cnf(c_0_55,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_52]),
    [final]).

cnf(c_0_56,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28]),
    [final]).

cnf(c_0_57,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_39]),
    [final]).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28]),
    [final]).

cnf(c_0_60,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_59]),
    [final]).

fof(c_0_62,negated_conjecture,(
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

cnf(c_0_63,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X5,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_61]),
    [final]).

fof(c_0_65,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).

cnf(c_0_66,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_63]),
    [final]).

cnf(c_0_67,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_66]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X3,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_69]),c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_70])).

cnf(c_0_73,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_71,c_0_41]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_41])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X4)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X3,esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76]),
    [final]).

cnf(c_0_81,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X4)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_41]),
    [final]).

cnf(c_0_82,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_41]),
    [final]).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_28])).

cnf(c_0_85,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X5,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_61]),
    [final]).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_41]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_76])).

cnf(c_0_89,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_41])).

cnf(c_0_90,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))) = k5_xboole_0(esk3_0,k1_xboole_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_58]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X3,esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))) = k5_xboole_0(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_80])).

cnf(c_0_96,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_93]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_xboole_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_95])).

cnf(c_0_99,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_96]),c_0_41])])).

cnf(c_0_100,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32])]),
    [final]).

fof(c_0_101,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | k4_xboole_0(k2_xboole_0(X10,X11),X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_61])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_41])).

cnf(c_0_104,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k7_subset_1(X3,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_98]),
    [final]).

cnf(c_0_105,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_41])).

cnf(c_0_106,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_28]),
    [final]).

cnf(c_0_107,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_108,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X5) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35]),
    [final]).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_41]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X3,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_104])).

cnf(c_0_112,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_58]),c_0_28])).

cnf(c_0_113,plain,
    ( r1_xboole_0(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_39]),
    [final]).

cnf(c_0_114,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_25]),c_0_21])).

cnf(c_0_115,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_108])).

cnf(c_0_116,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32]),
    [final]).

cnf(c_0_117,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_44]),
    [final]).

cnf(c_0_118,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_42]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_80]),c_0_28])).

cnf(c_0_120,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_41]),
    [final]).

cnf(c_0_121,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113]),
    [final]).

cnf(c_0_122,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_114,c_0_28])).

cnf(c_0_123,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44]),
    [final]).

cnf(c_0_124,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_115,c_0_41]),
    [final]).

cnf(c_0_125,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) = k7_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_116]),
    [final]).

cnf(c_0_126,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42]),
    [final]).

cnf(c_0_127,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_129,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_80])).

cnf(c_0_131,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(X2,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,X3)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_120])).

cnf(c_0_132,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k7_subset_1(X5,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46]),
    [final]).

cnf(c_0_133,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_121]),
    [final]).

cnf(c_0_134,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_122,c_0_38]),
    [final]).

cnf(c_0_135,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_41]),
    [final]).

cnf(c_0_136,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_64])).

cnf(c_0_137,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k7_subset_1(X5,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_123]),
    [final]).

cnf(c_0_138,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_124])).

cnf(c_0_139,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_125])).

cnf(c_0_140,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_86])).

cnf(c_0_141,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_126]),
    [final]).

cnf(c_0_142,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_108])).

cnf(c_0_143,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_127]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,esk3_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_145,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_130])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_61])).

cnf(c_0_147,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_41])).

cnf(c_0_148,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_149,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_28]),
    [final]).

cnf(c_0_150,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_135])).

cnf(c_0_151,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_41]),
    [final]).

cnf(c_0_152,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_41]),
    [final]).

cnf(c_0_153,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_137])).

cnf(c_0_154,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_138,c_0_41]),
    [final]).

cnf(c_0_155,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_139,c_0_41]),
    [final]).

cnf(c_0_156,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_140,c_0_41]),
    [final]).

cnf(c_0_157,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_123,c_0_141]),
    [final]).

cnf(c_0_158,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_142,c_0_41]),
    [final]).

cnf(c_0_159,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_143])).

cnf(c_0_160,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_144])).

cnf(c_0_161,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))) = k5_xboole_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_80]),
    [final]).

cnf(c_0_162,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_146,c_0_41]),
    [final]).

cnf(c_0_163,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_80]),
    [final]).

cnf(c_0_164,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_148,c_0_41])).

cnf(c_0_165,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k7_subset_1(X5,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_46]),
    [final]).

cnf(c_0_166,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k7_subset_1(X5,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_123]),
    [final]).

cnf(c_0_167,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) = k7_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_116]),
    [final]).

cnf(c_0_168,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_39]),
    [final]).

cnf(c_0_169,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_150,c_0_41]),
    [final]).

cnf(c_0_170,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_151])).

cnf(c_0_171,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_152])).

cnf(c_0_172,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_135])).

cnf(c_0_173,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_153,c_0_41]),
    [final]).

cnf(c_0_174,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X4) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_175,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38]),
    [final]).

cnf(c_0_176,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_134,c_0_39]),
    [final]).

cnf(c_0_177,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_35]),
    [final]).

cnf(c_0_178,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_118]),
    [final]).

cnf(c_0_179,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_117]),
    [final]).

cnf(c_0_180,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X4) ),
    inference(spm,[status(thm)],[c_0_61,c_0_126]),
    [final]).

cnf(c_0_181,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_156])).

cnf(c_0_182,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_143]),c_0_28])).

cnf(c_0_183,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_157]),c_0_28])).

cnf(c_0_184,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_158])).

cnf(c_0_185,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_47]),
    [final]).

cnf(c_0_186,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_61]),
    [final]).

cnf(c_0_187,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_41])).

cnf(c_0_188,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_116]),
    [final]).

cnf(c_0_189,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_190,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_161]),
    [final]).

cnf(c_0_191,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_xboole_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_192,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_164,c_0_41]),
    [final]).

cnf(c_0_193,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_165]),c_0_28])).

cnf(c_0_194,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_132]),c_0_28])).

cnf(c_0_195,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_166]),c_0_28])).

cnf(c_0_196,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_137]),c_0_28])).

cnf(c_0_197,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_167])).

cnf(c_0_198,plain,
    ( k7_subset_1(X1,X2,k3_tarski(k2_tarski(X2,X3))) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32]),
    [final]).

cnf(c_0_199,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_123]),
    [final]).

cnf(c_0_200,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_82])).

cnf(c_0_201,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_170,c_0_41]),
    [final]).

cnf(c_0_202,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_171,c_0_41]),
    [final]).

cnf(c_0_203,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_172,c_0_41]),
    [final]).

cnf(c_0_204,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_133,c_0_173])).

cnf(c_0_205,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1))))) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_174,c_0_41])).

cnf(c_0_206,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_134,c_0_175]),
    [final]).

cnf(c_0_207,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_123]),
    [final]).

cnf(c_0_208,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_177])).

cnf(c_0_209,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_176,c_0_178]),
    [final]).

cnf(c_0_210,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_179]),
    [final]).

cnf(c_0_211,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_176,c_0_180]),
    [final]).

cnf(c_0_212,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_181,c_0_41]),
    [final]).

cnf(c_0_213,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_182,c_0_41]),
    [final]).

cnf(c_0_214,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_183,c_0_41]),
    [final]).

cnf(c_0_215,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X4)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_64])).

cnf(c_0_216,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_184,c_0_41]),
    [final]).

cnf(c_0_217,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_185]),
    [final]).

cnf(c_0_218,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_186])).

cnf(c_0_219,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_41]),
    [final]).

cnf(c_0_220,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_188,c_0_86])).

cnf(c_0_221,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_188,c_0_64])).

cnf(c_0_222,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_188,c_0_64])).

cnf(c_0_223,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_188,c_0_108])).

cnf(c_0_224,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32]),
    [final]).

cnf(c_0_225,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_152])).

cnf(c_0_226,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_struct_0(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_128]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_227,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_189]),c_0_80])]),
    [final]).

cnf(c_0_228,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,k2_struct_0(esk1_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_189]),
    [final]).

cnf(c_0_229,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_189]),c_0_76])]),
    [final]).

cnf(c_0_230,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_124])).

cnf(c_0_231,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X3,esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_68])).

cnf(c_0_232,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_94])).

cnf(c_0_233,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k7_subset_1(X3,esk2_0,esk3_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_190]),
    [final]).

cnf(c_0_234,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_xboole_0) = k7_subset_1(esk3_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_191,c_0_76]),
    [final]).

cnf(c_0_235,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_192,c_0_192]),
    [final]).

cnf(c_0_236,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_237,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_93]),
    [final]).

cnf(c_0_238,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_193,c_0_41]),
    [final]).

cnf(c_0_239,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_194,c_0_41]),
    [final]).

cnf(c_0_240,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_195,c_0_41]),
    [final]).

cnf(c_0_241,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_196,c_0_41]),
    [final]).

cnf(c_0_242,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_197,c_0_41]),
    [final]).

cnf(c_0_243,plain,
    ( k7_subset_1(X1,X2,k4_subset_1(X3,X4,X2)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_198,c_0_52]),
    [final]).

cnf(c_0_244,plain,
    ( k7_subset_1(X1,X2,k4_subset_1(X3,X2,X4)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_44]),
    [final]).

cnf(c_0_245,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_199]),c_0_28])).

cnf(c_0_246,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_58]),
    [final]).

cnf(c_0_247,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_201,c_0_32]),
    [final]).

cnf(c_0_248,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_202,c_0_32]),
    [final]).

cnf(c_0_249,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_203,c_0_32]),
    [final]).

cnf(c_0_250,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_154,c_0_32]),
    [final]).

cnf(c_0_251,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_204,c_0_41]),
    [final]).

cnf(c_0_252,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_118]),
    [final]).

cnf(c_0_253,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27]),
    [final]).

cnf(c_0_254,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_117]),
    [final]).

cnf(c_0_255,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_126]),
    [final]).

cnf(c_0_256,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47]),
    [final]).

cnf(c_0_257,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_53]),c_0_32])).

cnf(c_0_258,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_206,c_0_86])).

cnf(c_0_259,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_206,c_0_64])).

cnf(c_0_260,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_206,c_0_64])).

cnf(c_0_261,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_206,c_0_108])).

cnf(c_0_262,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_207])).

cnf(c_0_263,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_86,c_0_207])).

cnf(c_0_264,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_108,c_0_207])).

cnf(c_0_265,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_188,c_0_52]),
    [final]).

cnf(c_0_266,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_61]),
    [final]).

cnf(c_0_267,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_208,c_0_41]),
    [final]).

cnf(c_0_268,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_209,c_0_41]),
    [final]).

cnf(c_0_269,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_210,c_0_41]),
    [final]).

cnf(c_0_270,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_211,c_0_41]),
    [final]).

cnf(c_0_271,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_213]),
    [final]).

cnf(c_0_272,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_203,c_0_214]),
    [final]).

cnf(c_0_273,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X4)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_215,c_0_41]),
    [final]).

cnf(c_0_274,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_216,c_0_214]),
    [final]).

cnf(c_0_275,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_217,c_0_41]),
    [final]).

cnf(c_0_276,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_218,c_0_41]),
    [final]).

cnf(c_0_277,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = k7_subset_1(X3,k4_subset_1(X1,X2,X2),X4)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X5)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_219]),c_0_41])])).

cnf(c_0_278,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_219,c_0_39]),
    [final]).

cnf(c_0_279,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_220,c_0_41]),
    [final]).

cnf(c_0_280,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_221,c_0_41]),
    [final]).

cnf(c_0_281,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_222,c_0_41]),
    [final]).

cnf(c_0_282,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_223,c_0_41]),
    [final]).

cnf(c_0_283,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_38]),
    [final]).

cnf(c_0_284,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_32]),
    [final]).

cnf(c_0_285,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_175,c_0_224]),
    [final]).

cnf(c_0_286,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_225,c_0_41]),
    [final]).

cnf(c_0_287,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_288,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_289,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_230,c_0_91])).

cnf(c_0_290,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38]),
    [final]).

cnf(c_0_291,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_231])).

cnf(c_0_292,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_224]),
    [final]).

cnf(c_0_293,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_232,c_0_41])).

cnf(c_0_294,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k7_subset_1(X3,esk2_0,esk3_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_190]),
    [final]).

cnf(c_0_295,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_233])).

cnf(c_0_296,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_231])).

cnf(c_0_297,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k7_subset_1(X3,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_98]),
    [final]).

cnf(c_0_298,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_98,c_0_234]),
    [final]).

cnf(c_0_299,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X3) ),
    inference(spm,[status(thm)],[c_0_115,c_0_91])).

cnf(c_0_300,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X3) ),
    inference(spm,[status(thm)],[c_0_115,c_0_68])).

cnf(c_0_301,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_302,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_303,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_304,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_59]),
    [final]).

cnf(c_0_305,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32]),
    [final]).

cnf(c_0_306,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X3,esk3_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_163])).

cnf(c_0_307,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_235]),c_0_41])]),
    [final]).

cnf(c_0_308,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_309,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_310,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_237]),c_0_41])]),
    [final]).

cnf(c_0_311,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_238])).

cnf(c_0_312,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_239])).

cnf(c_0_313,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_240])).

cnf(c_0_314,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_241])).

cnf(c_0_315,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)),k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_242,c_0_32]),
    [final]).

cnf(c_0_316,plain,
    ( k7_subset_1(X1,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_38]),
    [final]).

cnf(c_0_317,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_32]),
    [final]).

cnf(c_0_318,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_243])).

cnf(c_0_319,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_244])).

cnf(c_0_320,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_235]),c_0_41])])).

cnf(c_0_321,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_235]),c_0_41])])).

cnf(c_0_322,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_236]),c_0_41])])).

cnf(c_0_323,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_236]),c_0_41])])).

cnf(c_0_324,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_236]),c_0_41])])).

cnf(c_0_325,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_236]),c_0_41])])).

cnf(c_0_326,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_237]),c_0_41])])).

cnf(c_0_327,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_237]),c_0_41])])).

cnf(c_0_328,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_245,c_0_41]),
    [final]).

cnf(c_0_329,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_246,c_0_28]),
    [final]).

cnf(c_0_330,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_28]),
    [final]).

cnf(c_0_331,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_247,c_0_32]),
    [final]).

cnf(c_0_332,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_248,c_0_32]),
    [final]).

cnf(c_0_333,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_249,c_0_32]),
    [final]).

cnf(c_0_334,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_250,c_0_32]),
    [final]).

cnf(c_0_335,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_66]),
    [final]).

cnf(c_0_336,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_251])).

cnf(c_0_337,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_176,c_0_252]),
    [final]).

cnf(c_0_338,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_339,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X4))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_254]),
    [final]).

cnf(c_0_340,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_176,c_0_255]),
    [final]).

cnf(c_0_341,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X5)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_256]),
    [final]).

cnf(c_0_342,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_257,c_0_53]),
    [final]).

cnf(c_0_343,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_123]),c_0_28])).

cnf(c_0_344,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) = k7_subset_1(X4,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_175]),
    [final]).

cnf(c_0_345,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) = k7_subset_1(X4,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_175]),
    [final]).

cnf(c_0_346,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_258,c_0_41]),
    [final]).

cnf(c_0_347,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_259,c_0_41]),
    [final]).

cnf(c_0_348,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_260,c_0_41]),
    [final]).

cnf(c_0_349,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_261,c_0_41]),
    [final]).

cnf(c_0_350,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_254]),
    [final]).

cnf(c_0_351,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_262,c_0_41]),
    [final]).

cnf(c_0_352,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_263,c_0_41]),
    [final]).

cnf(c_0_353,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_264,c_0_41]),
    [final]).

cnf(c_0_354,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_265]),c_0_28])).

cnf(c_0_355,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_266])).

cnf(c_0_356,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_267,c_0_32]),
    [final]).

cnf(c_0_357,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X5,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_268]),c_0_41])])).

cnf(c_0_358,plain,
    ( r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_39]),
    [final]).

cnf(c_0_359,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X5,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_269]),c_0_41])])).

cnf(c_0_360,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X5,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_270]),c_0_41])])).

cnf(c_0_361,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_271])).

cnf(c_0_362,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_151,c_0_272])).

cnf(c_0_363,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X5,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_135,c_0_272])).

cnf(c_0_364,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X5)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_273,c_0_274])).

cnf(c_0_365,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X5)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_158,c_0_274])).

cnf(c_0_366,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X5,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_275]),c_0_41])])).

cnf(c_0_367,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)),k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_276,c_0_32]),
    [final]).

cnf(c_0_368,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_277,c_0_41]),
    [final]).

cnf(c_0_369,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_53]),c_0_100])])).

cnf(c_0_370,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_207]),c_0_28])).

cnf(c_0_371,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_118]),
    [final]).

cnf(c_0_372,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_117]),
    [final]).

cnf(c_0_373,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3) ),
    inference(spm,[status(thm)],[c_0_123,c_0_126]),
    [final]).

cnf(c_0_374,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X2
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_279,c_0_41]),
    [final]).

cnf(c_0_375,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_280,c_0_41]),
    [final]).

cnf(c_0_376,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_281,c_0_41]),
    [final]).

cnf(c_0_377,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_282,c_0_41]),
    [final]).

cnf(c_0_378,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_135])).

cnf(c_0_379,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_135])).

cnf(c_0_380,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))
    | ~ r1_xboole_0(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_168]),
    [final]).

cnf(c_0_381,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)
    | ~ r1_xboole_0(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_168]),
    [final]).

cnf(c_0_382,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))
    | ~ r1_xboole_0(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_176]),
    [final]).

cnf(c_0_383,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)
    | ~ r1_xboole_0(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_176]),
    [final]).

cnf(c_0_384,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_35]),
    [final]).

cnf(c_0_385,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_283]),
    [final]).

cnf(c_0_386,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_175,c_0_284]),
    [final]).

cnf(c_0_387,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_285]),
    [final]).

cnf(c_0_388,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_389,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_390,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_151])).

cnf(c_0_391,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_392,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_393,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_394,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_395,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_287,c_0_28]),
    [final]).

cnf(c_0_396,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_288,c_0_28]),
    [final]).

cnf(c_0_397,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_91])).

cnf(c_0_398,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_171,c_0_91])).

cnf(c_0_399,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_91])).

cnf(c_0_400,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_289,c_0_226]),
    [final]).

cnf(c_0_401,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_290,c_0_284]),
    [final]).

cnf(c_0_402,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_68])).

cnf(c_0_403,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_404,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_291,c_0_41])).

cnf(c_0_405,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_406,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_292])).

cnf(c_0_407,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_293,c_0_226]),
    [final]).

cnf(c_0_408,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_230,c_0_68])).

cnf(c_0_409,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_294])).

cnf(c_0_410,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_295,c_0_41]),
    [final]).

cnf(c_0_411,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_123,c_0_207])).

cnf(c_0_412,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_296,c_0_41])).

cnf(c_0_413,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_297])).

cnf(c_0_414,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_298]),c_0_80])])).

cnf(c_0_415,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,k1_xboole_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_68])).

cnf(c_0_416,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_228]),
    [final]).

cnf(c_0_417,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_228]),
    [final]).

cnf(c_0_418,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X3)
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_91])).

cnf(c_0_419,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X3)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_68])).

cnf(c_0_420,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0)) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_226]),
    [final]).

cnf(c_0_421,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X3,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X3,esk2_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_91])).

cnf(c_0_422,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,k2_struct_0(esk1_0)) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_228]),
    [final]).

cnf(c_0_423,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X3,esk3_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X3,esk3_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_68])).

cnf(c_0_424,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X3,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_91])).

cnf(c_0_425,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_299,c_0_226]),
    [final]).

cnf(c_0_426,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_226]),
    [final]).

cnf(c_0_427,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_300,c_0_228]),
    [final]).

cnf(c_0_428,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_228]),
    [final]).

cnf(c_0_429,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_301]),
    [final]).

cnf(c_0_430,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_302]),
    [final]).

cnf(c_0_431,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_303]),
    [final]).

cnf(c_0_432,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_302]),
    [final]).

cnf(c_0_433,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_301]),
    [final]).

cnf(c_0_434,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_435,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk3_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_228]),c_0_229]),
    [final]).

cnf(c_0_436,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_226]),c_0_227]),
    [final]).

cnf(c_0_437,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_304,c_0_28]),
    [final]).

cnf(c_0_438,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_305,c_0_28]),
    [final]).

cnf(c_0_439,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_306,c_0_68]),
    [final]).

cnf(c_0_440,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_307,c_0_39]),
    [final]).

cnf(c_0_441,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_308,c_0_39]),
    [final]).

cnf(c_0_442,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_309,c_0_39]),
    [final]).

cnf(c_0_443,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_310,c_0_39]),
    [final]).

cnf(c_0_444,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_311,c_0_41]),
    [final]).

cnf(c_0_445,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_312,c_0_41]),
    [final]).

cnf(c_0_446,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_313,c_0_41]),
    [final]).

cnf(c_0_447,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3) ),
    inference(spm,[status(thm)],[c_0_314,c_0_41]),
    [final]).

cnf(c_0_448,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)),k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_315,c_0_52]),
    [final]).

cnf(c_0_449,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_235]),c_0_41])]),
    [final]).

cnf(c_0_450,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_451,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_452,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_237]),c_0_41])]),
    [final]).

cnf(c_0_453,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)),k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_315,c_0_39]),
    [final]).

cnf(c_0_454,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4))) ),
    inference(spm,[status(thm)],[c_0_317,c_0_52]),
    [final]).

cnf(c_0_455,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4))) ),
    inference(spm,[status(thm)],[c_0_317,c_0_39]),
    [final]).

cnf(c_0_456,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_318,c_0_41]),
    [final]).

cnf(c_0_457,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_319,c_0_41]),
    [final]).

cnf(c_0_458,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)),k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_315,c_0_28]),
    [final]).

cnf(c_0_459,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_320,c_0_58]),
    [final]).

cnf(c_0_460,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_321,c_0_58]),
    [final]).

cnf(c_0_461,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_322,c_0_58]),
    [final]).

cnf(c_0_462,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_58]),
    [final]).

cnf(c_0_463,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3))) ),
    inference(spm,[status(thm)],[c_0_317,c_0_28]),
    [final]).

cnf(c_0_464,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_324,c_0_113]),
    [final]).

cnf(c_0_465,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_325,c_0_113]),
    [final]).

cnf(c_0_466,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_326,c_0_113]),
    [final]).

cnf(c_0_467,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_327,c_0_113]),
    [final]).

cnf(c_0_468,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_328,c_0_329]),
    [final]).

cnf(c_0_469,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_328,c_0_330]),
    [final]).

cnf(c_0_470,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_471,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_472,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_240]),
    [final]).

cnf(c_0_473,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_93]),
    [final]).

cnf(c_0_474,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_331,c_0_52]),
    [final]).

cnf(c_0_475,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_331,c_0_39]),
    [final]).

cnf(c_0_476,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_332,c_0_52]),
    [final]).

cnf(c_0_477,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_332,c_0_39]),
    [final]).

cnf(c_0_478,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_333,c_0_52]),
    [final]).

cnf(c_0_479,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_333,c_0_39]),
    [final]).

cnf(c_0_480,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_334,c_0_52]),
    [final]).

cnf(c_0_481,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_334,c_0_39]),
    [final]).

cnf(c_0_482,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_335])).

cnf(c_0_483,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_335])).

cnf(c_0_484,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_335]),c_0_28])).

cnf(c_0_485,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_69])).

cnf(c_0_486,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_69])).

cnf(c_0_487,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_165])).

cnf(c_0_488,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_165])).

cnf(c_0_489,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_336,c_0_58]),
    [final]).

cnf(c_0_490,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_132])).

cnf(c_0_491,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_132])).

cnf(c_0_492,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_337,c_0_41]),
    [final]).

cnf(c_0_493,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_338]),c_0_28])).

cnf(c_0_494,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_339,c_0_41]),
    [final]).

cnf(c_0_495,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_340,c_0_41]),
    [final]).

cnf(c_0_496,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_341,c_0_41]),
    [final]).

cnf(c_0_497,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_498,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_39]),c_0_342])).

cnf(c_0_499,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_166])).

cnf(c_0_500,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_166])).

cnf(c_0_501,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_251])).

cnf(c_0_502,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_137])).

cnf(c_0_503,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_328,c_0_93]),
    [final]).

cnf(c_0_504,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_343,c_0_41]),
    [final]).

cnf(c_0_505,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_201,c_0_213]),
    [final]).

cnf(c_0_506,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3) ),
    inference(spm,[status(thm)],[c_0_154,c_0_214]),
    [final]).

cnf(c_0_507,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_201,c_0_38]),
    [final]).

cnf(c_0_508,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))),k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_242,c_0_38]),
    [final]).

cnf(c_0_509,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_202,c_0_38]),
    [final]).

cnf(c_0_510,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_38]),
    [final]).

cnf(c_0_511,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_203,c_0_38]),
    [final]).

cnf(c_0_512,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_154,c_0_38]),
    [final]).

cnf(c_0_513,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_344])).

cnf(c_0_514,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_344])).

cnf(c_0_515,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_345])).

cnf(c_0_516,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_345])).

cnf(c_0_517,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_167])).

cnf(c_0_518,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_125])).

cnf(c_0_519,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X1
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_346,c_0_41]),
    [final]).

cnf(c_0_520,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_347,c_0_41]),
    [final]).

cnf(c_0_521,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_348,c_0_41]),
    [final]).

cnf(c_0_522,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_349,c_0_41]),
    [final]).

cnf(c_0_523,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_350,c_0_41]),
    [final]).

cnf(c_0_524,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_351,c_0_41]),
    [final]).

cnf(c_0_525,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_352,c_0_41]),
    [final]).

cnf(c_0_526,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_353,c_0_41]),
    [final]).

cnf(c_0_527,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_354,c_0_41]),
    [final]).

cnf(c_0_528,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_355,c_0_41]),
    [final]).

cnf(c_0_529,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_356,c_0_28]),
    [final]).

cnf(c_0_530,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_247,c_0_38]),
    [final]).

cnf(c_0_531,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_357,c_0_358]),c_0_28])).

cnf(c_0_532,plain,
    ( r1_xboole_0(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_39]),
    [final]).

cnf(c_0_533,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_248,c_0_38]),
    [final]).

cnf(c_0_534,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_249,c_0_38]),
    [final]).

cnf(c_0_535,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359,c_0_58]),c_0_28])).

cnf(c_0_536,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_250,c_0_38]),
    [final]).

cnf(c_0_537,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_360,c_0_358]),c_0_28])).

cnf(c_0_538,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_361,c_0_41]),
    [final]).

cnf(c_0_539,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_362,c_0_41]),
    [final]).

cnf(c_0_540,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_363,c_0_41]),
    [final]).

cnf(c_0_541,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_364,c_0_41]),
    [final]).

cnf(c_0_542,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_365,c_0_41]),
    [final]).

cnf(c_0_543,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_366,c_0_58]),c_0_28])).

cnf(c_0_544,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_367,c_0_52]),
    [final]).

cnf(c_0_545,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_367,c_0_39]),
    [final]).

cnf(c_0_546,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_356,c_0_52]),
    [final]).

cnf(c_0_547,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_356,c_0_39]),
    [final]).

cnf(c_0_548,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_368,c_0_39]),
    [final]).

cnf(c_0_549,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_369,c_0_41])).

cnf(c_0_550,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_370,c_0_41]),
    [final]).

cnf(c_0_551,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_371]),c_0_28])).

cnf(c_0_552,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_372]),c_0_28])).

cnf(c_0_553,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_373]),c_0_28])).

cnf(c_0_554,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_374]),c_0_41])]),
    [final]).

cnf(c_0_555,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_374]),c_0_41])]),
    [final]).

cnf(c_0_556,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_375]),c_0_41])]),
    [final]).

cnf(c_0_557,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_375]),c_0_41])]),
    [final]).

cnf(c_0_558,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_376]),c_0_41])]),
    [final]).

cnf(c_0_559,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_376]),c_0_41])]),
    [final]).

cnf(c_0_560,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_377]),c_0_41])]),
    [final]).

cnf(c_0_561,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_377]),c_0_41])]),
    [final]).

cnf(c_0_562,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_156])).

cnf(c_0_563,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_156])).

cnf(c_0_564,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_151])).

cnf(c_0_565,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_151])).

cnf(c_0_566,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_273])).

cnf(c_0_567,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_273])).

cnf(c_0_568,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_81])).

cnf(c_0_569,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_81])).

cnf(c_0_570,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_378,c_0_41]),
    [final]).

cnf(c_0_571,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_379,c_0_41]),
    [final]).

cnf(c_0_572,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_158])).

cnf(c_0_573,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_158])).

cnf(c_0_574,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_206,c_0_124])).

cnf(c_0_575,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_124])).

cnf(c_0_576,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_380])).

cnf(c_0_577,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_380])).

cnf(c_0_578,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_381])).

cnf(c_0_579,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_381])).

cnf(c_0_580,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_382])).

cnf(c_0_581,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_382])).

cnf(c_0_582,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_383])).

cnf(c_0_583,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_383])).

cnf(c_0_584,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))),k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_276,c_0_38]),
    [final]).

cnf(c_0_585,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_267,c_0_38]),
    [final]).

cnf(c_0_586,plain,
    ( X1 = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X1)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_374]),c_0_41])]),c_0_75]),
    [final]).

cnf(c_0_587,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_46]),c_0_28])).

cnf(c_0_588,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X1)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_376]),c_0_41])]),c_0_75]),
    [final]).

cnf(c_0_589,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_377]),c_0_41])]),c_0_75]),
    [final]).

cnf(c_0_590,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_266])).

cnf(c_0_591,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_186])).

cnf(c_0_592,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_384])).

cnf(c_0_593,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_384])).

cnf(c_0_594,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0))))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_177])).

cnf(c_0_595,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,X3))
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_371]),
    [final]).

cnf(c_0_596,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_372]),
    [final]).

cnf(c_0_597,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_373]),
    [final]).

cnf(c_0_598,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_168,c_0_49]),
    [final]).

cnf(c_0_599,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_385]),
    [final]).

cnf(c_0_600,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_386]),
    [final]).

cnf(c_0_601,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_387,c_0_28]),
    [final]).

cnf(c_0_602,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_388,c_0_28]),
    [final]).

cnf(c_0_603,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_389,c_0_28]),
    [final]).

cnf(c_0_604,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_201,c_0_201])).

cnf(c_0_605,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_390,c_0_41]),
    [final]).

cnf(c_0_606,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_391,c_0_28]),
    [final]).

cnf(c_0_607,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_392,c_0_28]),
    [final]).

cnf(c_0_608,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_393,c_0_28]),
    [final]).

cnf(c_0_609,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_394,c_0_28]),
    [final]).

cnf(c_0_610,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_395,c_0_202])).

cnf(c_0_611,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_226]),
    [final]).

cnf(c_0_612,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_396,c_0_202])).

cnf(c_0_613,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_228]),
    [final]).

cnf(c_0_614,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_395,c_0_169])).

cnf(c_0_615,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_396,c_0_169])).

cnf(c_0_616,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X4)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_154])).

cnf(c_0_617,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_230,c_0_41]),
    [final]).

cnf(c_0_618,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X3)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_397,c_0_398])).

cnf(c_0_619,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_284,c_0_283]),
    [final]).

cnf(c_0_620,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_399,c_0_226]),
    [final]).

cnf(c_0_621,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_399,c_0_226]),
    [final]).

cnf(c_0_622,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_400,c_0_399])).

cnf(c_0_623,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_401]),
    [final]).

cnf(c_0_624,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X3)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_402,c_0_403])).

cnf(c_0_625,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X3,esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_404,c_0_405])).

cnf(c_0_626,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_118]),
    [final]).

cnf(c_0_627,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_117]),
    [final]).

cnf(c_0_628,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_406,c_0_41]),
    [final]).

cnf(c_0_629,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X3)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_397,c_0_397])).

cnf(c_0_630,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_407,c_0_397]),c_0_75])).

cnf(c_0_631,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X3)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_402,c_0_402])).

cnf(c_0_632,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_400]),c_0_75])).

cnf(c_0_633,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_224,c_0_290]),
    [final]).

cnf(c_0_634,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_407,c_0_289]),c_0_75])).

cnf(c_0_635,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_408,c_0_228]),
    [final]).

cnf(c_0_636,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_409,c_0_41]),
    [final]).

cnf(c_0_637,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_294])).

cnf(c_0_638,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_410,c_0_226]),
    [final]).

cnf(c_0_639,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_411,c_0_41]),
    [final]).

cnf(c_0_640,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X3,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_404])).

cnf(c_0_641,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_412,c_0_228]),
    [final]).

cnf(c_0_642,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_413,c_0_41]),
    [final]).

cnf(c_0_643,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_297])).

cnf(c_0_644,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_414,c_0_41]),
    [final]).

cnf(c_0_645,negated_conjecture,
    ( k7_subset_1(esk3_0,esk3_0,X1) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_306,c_0_41]),
    [final]).

cnf(c_0_646,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_298]),c_0_80])])).

cnf(c_0_647,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k5_xboole_0(esk3_0,k1_xboole_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_415,c_0_228])).

cnf(c_0_648,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_228]),
    [final]).

cnf(c_0_649,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_228]),
    [final]).

cnf(c_0_650,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_416])).

cnf(c_0_651,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_417])).

cnf(c_0_652,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_418,c_0_226]),
    [final]).

cnf(c_0_653,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_419,c_0_228]),
    [final]).

cnf(c_0_654,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_420,c_0_421])).

cnf(c_0_655,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_422,c_0_423])).

cnf(c_0_656,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_420,c_0_424])).

cnf(c_0_657,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_422,c_0_70])).

cnf(c_0_658,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_425,c_0_426]),
    [final]).

cnf(c_0_659,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_420,c_0_299])).

cnf(c_0_660,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_427,c_0_428]),
    [final]).

cnf(c_0_661,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_422,c_0_300])).

cnf(c_0_662,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0) = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_149,c_0_284]),
    [final]).

cnf(c_0_663,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_149,c_0_224]),
    [final]).

cnf(c_0_664,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_429,c_0_243])).

cnf(c_0_665,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_430,c_0_243])).

cnf(c_0_666,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_431,c_0_243])).

cnf(c_0_667,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_432,c_0_243])).

cnf(c_0_668,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_244,c_0_429])).

cnf(c_0_669,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_244,c_0_433])).

cnf(c_0_670,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_244,c_0_430])).

cnf(c_0_671,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_244,c_0_432])).

cnf(c_0_672,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_429])).

cnf(c_0_673,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_429])).

cnf(c_0_674,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_433])).

cnf(c_0_675,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_433])).

cnf(c_0_676,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_430])).

cnf(c_0_677,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_430])).

cnf(c_0_678,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_432])).

cnf(c_0_679,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_432])).

cnf(c_0_680,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_316,c_0_429])).

cnf(c_0_681,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_198,c_0_429])).

cnf(c_0_682,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_316,c_0_433])).

cnf(c_0_683,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_198,c_0_433])).

cnf(c_0_684,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_316,c_0_430])).

cnf(c_0_685,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_198,c_0_430])).

cnf(c_0_686,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_302,c_0_303]),
    [final]).

cnf(c_0_687,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_301,c_0_434]),
    [final]).

cnf(c_0_688,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_316,c_0_432])).

cnf(c_0_689,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_198,c_0_432])).

cnf(c_0_690,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_302,c_0_301]),
    [final]).

cnf(c_0_691,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_91])).

cnf(c_0_692,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_91])).

cnf(c_0_693,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_435,c_0_35])).

cnf(c_0_694,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_436,c_0_35])).

cnf(c_0_695,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_696,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_437,c_0_39]),
    [final]).

cnf(c_0_697,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_304,c_0_39]),
    [final]).

cnf(c_0_698,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k4_subset_1(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_438,c_0_39]),
    [final]).

cnf(c_0_699,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_305,c_0_39]),
    [final]).

cnf(c_0_700,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_257,c_0_28])).

cnf(c_0_701,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_439,c_0_80])).

cnf(c_0_702,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_440,c_0_52]),
    [final]).

cnf(c_0_703,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_440,c_0_39]),
    [final]).

cnf(c_0_704,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_441,c_0_52]),
    [final]).

cnf(c_0_705,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_441,c_0_39]),
    [final]).

cnf(c_0_706,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_442,c_0_52]),
    [final]).

cnf(c_0_707,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_442,c_0_39]),
    [final]).

cnf(c_0_708,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_443,c_0_52]),
    [final]).

cnf(c_0_709,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_443,c_0_39]),
    [final]).

cnf(c_0_710,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_235]),c_0_41])]),
    [final]).

cnf(c_0_711,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_235]),c_0_41])]),
    [final]).

cnf(c_0_712,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_713,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_714,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_715,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_236]),c_0_41])]),
    [final]).

cnf(c_0_716,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_237]),c_0_41])]),
    [final]).

cnf(c_0_717,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_237]),c_0_41])]),
    [final]).

cnf(c_0_718,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_444,c_0_28]),
    [final]).

cnf(c_0_719,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_445,c_0_28]),
    [final]).

cnf(c_0_720,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_446,c_0_28]),
    [final]).

cnf(c_0_721,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3) ),
    inference(spm,[status(thm)],[c_0_447,c_0_28]),
    [final]).

cnf(c_0_722,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X2,X3,k1_xboole_0)),k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_448,c_0_52]),
    [final]).

cnf(c_0_723,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X2,X3,k1_xboole_0),X5),k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_448,c_0_39]),
    [final]).

cnf(c_0_724,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_449,c_0_39]),
    [final]).

cnf(c_0_725,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_450,c_0_39]),
    [final]).

cnf(c_0_726,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_451,c_0_39]),
    [final]).

cnf(c_0_727,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_452,c_0_39]),
    [final]).

cnf(c_0_728,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X2,k1_xboole_0,X3)),k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_453,c_0_52]),
    [final]).

cnf(c_0_729,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X2,k1_xboole_0,X3),X5),k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_453,c_0_39]),
    [final]).

cnf(c_0_730,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X4,X5,k4_subset_1(X2,X3,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_454,c_0_52]),
    [final]).

cnf(c_0_731,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X4,k4_subset_1(X2,X3,k1_xboole_0),X5)) ),
    inference(spm,[status(thm)],[c_0_454,c_0_39]),
    [final]).

cnf(c_0_732,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X4,X5,k4_subset_1(X2,k1_xboole_0,X3))) ),
    inference(spm,[status(thm)],[c_0_455,c_0_52]),
    [final]).

cnf(c_0_733,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X4,k4_subset_1(X2,k1_xboole_0,X3),X5)) ),
    inference(spm,[status(thm)],[c_0_455,c_0_39]),
    [final]).

cnf(c_0_734,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)),k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_444]),
    [final]).

cnf(c_0_735,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4),k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_444]),
    [final]).

cnf(c_0_736,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_445]),
    [final]).

cnf(c_0_737,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_445]),
    [final]).

cnf(c_0_738,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)),k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_446]),
    [final]).

cnf(c_0_739,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4),k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_446]),
    [final]).

cnf(c_0_740,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_447]),
    [final]).

cnf(c_0_741,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_447]),
    [final]).

cnf(c_0_742,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X2,k1_xboole_0))),k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_458,c_0_52]),
    [final]).

cnf(c_0_743,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)),X4),k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_458,c_0_39]),
    [final]).

cnf(c_0_744,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_459,c_0_39]),
    [final]).

cnf(c_0_745,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_460,c_0_39]),
    [final]).

cnf(c_0_746,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(k1_xboole_0,X2))),k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_242]),
    [final]).

cnf(c_0_747,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)),X4),k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_457,c_0_242]),
    [final]).

cnf(c_0_748,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_461,c_0_39]),
    [final]).

cnf(c_0_749,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_462,c_0_39]),
    [final]).

cnf(c_0_750,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X2,k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_463,c_0_52]),
    [final]).

cnf(c_0_751,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k4_subset_1(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)),X4)) ),
    inference(spm,[status(thm)],[c_0_463,c_0_39]),
    [final]).

cnf(c_0_752,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_464,c_0_39]),
    [final]).

cnf(c_0_753,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_465,c_0_39]),
    [final]).

cnf(c_0_754,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(k1_xboole_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_155]),
    [final]).

cnf(c_0_755,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)),X4)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_155]),
    [final]).

cnf(c_0_756,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_466,c_0_39]),
    [final]).

cnf(c_0_757,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_467,c_0_39]),
    [final]).

cnf(c_0_758,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_338]),c_0_41])]),
    [final]).

cnf(c_0_759,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_338]),c_0_41])]),
    [final]).

cnf(c_0_760,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_96]),c_0_41])]),
    [final]).

cnf(c_0_761,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_96]),c_0_41])]),
    [final]).

cnf(c_0_762,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_246]),
    [final]).

cnf(c_0_763,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_246]),
    [final]).

cnf(c_0_764,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_82]),
    [final]).

cnf(c_0_765,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_82]),
    [final]).

cnf(c_0_766,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_468,c_0_28]),
    [final]).

cnf(c_0_767,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_469,c_0_28]),
    [final]).

cnf(c_0_768,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_470,c_0_39]),
    [final]).

cnf(c_0_769,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_471,c_0_39]),
    [final]).

cnf(c_0_770,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k7_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_472,c_0_39]),
    [final]).

cnf(c_0_771,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_473,c_0_39]),
    [final]).

cnf(c_0_772,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_474,c_0_52]),
    [final]).

cnf(c_0_773,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_474,c_0_39]),
    [final]).

cnf(c_0_774,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_475,c_0_52]),
    [final]).

cnf(c_0_775,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_475,c_0_39]),
    [final]).

cnf(c_0_776,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_476,c_0_52]),
    [final]).

cnf(c_0_777,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_476,c_0_39]),
    [final]).

cnf(c_0_778,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_477,c_0_52]),
    [final]).

cnf(c_0_779,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_477,c_0_39]),
    [final]).

cnf(c_0_780,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_478,c_0_52]),
    [final]).

cnf(c_0_781,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_478,c_0_39]),
    [final]).

cnf(c_0_782,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_479,c_0_52]),
    [final]).

cnf(c_0_783,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_479,c_0_39]),
    [final]).

cnf(c_0_784,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_480,c_0_52]),
    [final]).

cnf(c_0_785,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_480,c_0_39]),
    [final]).

cnf(c_0_786,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_481,c_0_52]),
    [final]).

cnf(c_0_787,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_481,c_0_39]),
    [final]).

cnf(c_0_788,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_482,c_0_41]),
    [final]).

cnf(c_0_789,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_483,c_0_41]),
    [final]).

cnf(c_0_790,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_484,c_0_41]),
    [final]).

cnf(c_0_791,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_485,c_0_41]),
    [final]).

cnf(c_0_792,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_486,c_0_41]),
    [final]).

cnf(c_0_793,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))),k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_444,c_0_38]),
    [final]).

cnf(c_0_794,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)),k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_444,c_0_32]),
    [final]).

cnf(c_0_795,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_445,c_0_38]),
    [final]).

cnf(c_0_796,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) ),
    inference(spm,[status(thm)],[c_0_445,c_0_32]),
    [final]).

cnf(c_0_797,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))),k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_446,c_0_38]),
    [final]).

cnf(c_0_798,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)),k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_446,c_0_32]),
    [final]).

cnf(c_0_799,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_447,c_0_38]),
    [final]).

cnf(c_0_800,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_447,c_0_32]),
    [final]).

cnf(c_0_801,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_487,c_0_41]),
    [final]).

cnf(c_0_802,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_488,c_0_41]),
    [final]).

cnf(c_0_803,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_235,c_0_39]),
    [final]).

cnf(c_0_804,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_236,c_0_39]),
    [final]).

cnf(c_0_805,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_237,c_0_39]),
    [final]).

cnf(c_0_806,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_489]),
    [final]).

cnf(c_0_807,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_490,c_0_41]),
    [final]).

cnf(c_0_808,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4) ),
    inference(spm,[status(thm)],[c_0_491,c_0_41]),
    [final]).

cnf(c_0_809,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_489]),
    [final]).

cnf(c_0_810,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_251]),
    [final]).

cnf(c_0_811,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_251]),
    [final]).

cnf(c_0_812,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_268]),c_0_41])]),
    [final]).

cnf(c_0_813,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_268]),c_0_41])]),
    [final]).

cnf(c_0_814,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_338]),c_0_41])]),
    [final]).

cnf(c_0_815,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_338]),c_0_41])]),
    [final]).

cnf(c_0_816,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_492]),c_0_41])]),
    [final]).

cnf(c_0_817,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_492]),c_0_41])]),
    [final]).

cnf(c_0_818,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_493,c_0_41]),
    [final]).

cnf(c_0_819,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_269]),c_0_41])]),
    [final]).

cnf(c_0_820,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_269]),c_0_41])]),
    [final]).

cnf(c_0_821,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_494]),c_0_41])]),
    [final]).

cnf(c_0_822,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_494]),c_0_41])]),
    [final]).

cnf(c_0_823,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_270]),c_0_41])]),
    [final]).

cnf(c_0_824,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_270]),c_0_41])]),
    [final]).

cnf(c_0_825,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_495]),c_0_41])]),
    [final]).

cnf(c_0_826,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_495]),c_0_41])]),
    [final]).

cnf(c_0_827,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_275]),c_0_41])]),
    [final]).

cnf(c_0_828,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_275]),c_0_41])]),
    [final]).

cnf(c_0_829,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_496]),c_0_41])]),
    [final]).

cnf(c_0_830,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_496]),c_0_41])]),
    [final]).

cnf(c_0_831,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k7_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_338,c_0_39]),
    [final]).

cnf(c_0_832,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_489]),
    [final]).

cnf(c_0_833,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_121]),
    [final]).

cnf(c_0_834,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_497]),c_0_41])]),
    [final]).

cnf(c_0_835,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_497]),c_0_41])]),
    [final]).

cnf(c_0_836,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_497]),c_0_41])]),
    [final]).

cnf(c_0_837,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_497]),c_0_41])]),
    [final]).

cnf(c_0_838,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_192]),c_0_41])]),
    [final]).

cnf(c_0_839,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_497,c_0_39]),
    [final]).

cnf(c_0_840,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_498,c_0_41]),
    [final]).

cnf(c_0_841,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_499,c_0_41]),
    [final]).

cnf(c_0_842,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_500,c_0_41]),
    [final]).

cnf(c_0_843,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_121]),
    [final]).

cnf(c_0_844,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_501,c_0_58]),
    [final]).

cnf(c_0_845,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_489,c_0_38]),
    [final]).

cnf(c_0_846,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_489,c_0_32]),
    [final]).

cnf(c_0_847,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_251,c_0_28]),
    [final]).

cnf(c_0_848,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_251,c_0_38]),
    [final]).

cnf(c_0_849,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) ),
    inference(spm,[status(thm)],[c_0_251,c_0_32]),
    [final]).

cnf(c_0_850,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4) ),
    inference(spm,[status(thm)],[c_0_502,c_0_41]),
    [final]).

cnf(c_0_851,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_328,c_0_121]),
    [final]).

cnf(c_0_852,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))),k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_96]),c_0_41])]),
    [final]).

cnf(c_0_853,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X2,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_96]),c_0_41])]),
    [final]).

cnf(c_0_854,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_39]),
    [final]).

cnf(c_0_855,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_503]),c_0_41])]),
    [final]).

cnf(c_0_856,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_503]),c_0_41])]),
    [final]).

cnf(c_0_857,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_503]),c_0_41])]),
    [final]).

cnf(c_0_858,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_93]),
    [final]).

cnf(c_0_859,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_503]),c_0_41])]),
    [final]).

cnf(c_0_860,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_503,c_0_39]),
    [final]).

cnf(c_0_861,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_246,c_0_38]),
    [final]).

cnf(c_0_862,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_246,c_0_32]),
    [final]).

cnf(c_0_863,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_38]),
    [final]).

cnf(c_0_864,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_32]),
    [final]).

cnf(c_0_865,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_505]),
    [final]).

cnf(c_0_866,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_505]),
    [final]).

cnf(c_0_867,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_272]),
    [final]).

cnf(c_0_868,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_272]),
    [final]).

cnf(c_0_869,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_506]),
    [final]).

cnf(c_0_870,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_506]),
    [final]).

cnf(c_0_871,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_219]),c_0_41])]),
    [final]).

cnf(c_0_872,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_219]),c_0_41])]),
    [final]).

cnf(c_0_873,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_507]),
    [final]).

cnf(c_0_874,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))),k4_subset_1(X2,X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_508,c_0_52]),
    [final]).

cnf(c_0_875,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_457,c_0_507]),
    [final]).

cnf(c_0_876,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))),k4_subset_1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_508,c_0_39]),
    [final]).

cnf(c_0_877,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_247]),
    [final]).

cnf(c_0_878,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_457,c_0_247]),
    [final]).

cnf(c_0_879,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_509]),
    [final]).

cnf(c_0_880,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))
    | ~ m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k3_tarski(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_510,c_0_52]),
    [final]).

cnf(c_0_881,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_457,c_0_509]),
    [final]).

cnf(c_0_882,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_510,c_0_39]),
    [final]).

cnf(c_0_883,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_456,c_0_248]),
    [final]).

cnf(c_0_884,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_457,c_0_248]),
    [final]).

cnf(c_0_885,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_511]),
    [final]).

cnf(c_0_886,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_511]),
    [final]).

cnf(c_0_887,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_249]),
    [final]).

cnf(c_0_888,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_249]),
    [final]).

cnf(c_0_889,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_512]),
    [final]).

cnf(c_0_890,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_512]),
    [final]).

cnf(c_0_891,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_250]),
    [final]).

cnf(c_0_892,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_250]),
    [final]).

cnf(c_0_893,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_513,c_0_41]),
    [final]).

cnf(c_0_894,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_514,c_0_41]),
    [final]).

cnf(c_0_895,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_515,c_0_41]),
    [final]).

cnf(c_0_896,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_516,c_0_41]),
    [final]).

cnf(c_0_897,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_517,c_0_41]),
    [final]).

cnf(c_0_898,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))),k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_508,c_0_28]),
    [final]).

cnf(c_0_899,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_518,c_0_41]),
    [final]).

cnf(c_0_900,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_342,c_0_52]),
    [final]).

cnf(c_0_901,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_342,c_0_39]),
    [final]).

cnf(c_0_902,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0))))) ),
    inference(spm,[status(thm)],[c_0_510,c_0_28]),
    [final]).

cnf(c_0_903,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_519]),c_0_41])]),
    [final]).

cnf(c_0_904,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_519]),c_0_41])]),
    [final]).

cnf(c_0_905,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_374]),c_0_41])]),
    [final]).

cnf(c_0_906,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_374]),c_0_41])]),
    [final]).

cnf(c_0_907,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_520]),c_0_41])]),
    [final]).

cnf(c_0_908,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_520]),c_0_41])]),
    [final]).

cnf(c_0_909,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_375]),c_0_41])]),
    [final]).

cnf(c_0_910,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_375]),c_0_41])]),
    [final]).

cnf(c_0_911,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_521]),c_0_41])]),
    [final]).

cnf(c_0_912,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_521]),c_0_41])]),
    [final]).

cnf(c_0_913,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_376]),c_0_41])]),
    [final]).

cnf(c_0_914,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_376]),c_0_41])]),
    [final]).

cnf(c_0_915,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_522]),c_0_41])]),
    [final]).

cnf(c_0_916,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_522]),c_0_41])]),
    [final]).

cnf(c_0_917,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_377]),c_0_41])]),
    [final]).

cnf(c_0_918,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_377]),c_0_41])]),
    [final]).

cnf(c_0_919,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_523]),c_0_41])]),
    [final]).

cnf(c_0_920,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_523]),c_0_41])]),
    [final]).

cnf(c_0_921,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_524]),c_0_41])]),
    [final]).

cnf(c_0_922,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_524]),c_0_41])]),
    [final]).

cnf(c_0_923,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_525]),c_0_41])]),
    [final]).

cnf(c_0_924,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_525]),c_0_41])]),
    [final]).

cnf(c_0_925,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_526]),c_0_41])]),
    [final]).

cnf(c_0_926,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_526]),c_0_41])]),
    [final]).

cnf(c_0_927,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_42]),
    [final]).

cnf(c_0_928,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_212]),
    [final]).

cnf(c_0_929,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_201,c_0_42]),
    [final]).

cnf(c_0_930,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_201]),
    [final]).

cnf(c_0_931,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_286,c_0_42]),
    [final]).

cnf(c_0_932,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_286,c_0_42]),
    [final]).

cnf(c_0_933,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_286]),
    [final]).

cnf(c_0_934,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_286]),
    [final]).

cnf(c_0_935,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_42]),
    [final]).

cnf(c_0_936,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_202]),
    [final]).

cnf(c_0_937,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_203,c_0_42]),
    [final]).

cnf(c_0_938,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_504,c_0_203]),
    [final]).

cnf(c_0_939,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_216,c_0_42]),
    [final]).

cnf(c_0_940,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_216,c_0_44]),
    [final]).

cnf(c_0_941,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_154,c_0_42]),
    [final]).

cnf(c_0_942,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_154,c_0_44]),
    [final]).

cnf(c_0_943,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_201,c_0_527]),
    [final]).

cnf(c_0_944,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_286,c_0_527]),
    [final]).

cnf(c_0_945,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_203,c_0_527]),
    [final]).

cnf(c_0_946,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_154,c_0_527]),
    [final]).

cnf(c_0_947,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_212,c_0_527]),
    [final]).

cnf(c_0_948,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_202,c_0_527]),
    [final]).

cnf(c_0_949,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_286,c_0_527]),
    [final]).

cnf(c_0_950,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_216,c_0_527]),
    [final]).

cnf(c_0_951,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_201,c_0_328]),
    [final]).

cnf(c_0_952,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_286,c_0_328]),
    [final]).

cnf(c_0_953,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_203,c_0_328]),
    [final]).

cnf(c_0_954,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_328]),
    [final]).

cnf(c_0_955,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_212,c_0_328]),
    [final]).

cnf(c_0_956,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_202,c_0_328]),
    [final]).

cnf(c_0_957,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_286,c_0_328]),
    [final]).

cnf(c_0_958,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_216,c_0_328]),
    [final]).

cnf(c_0_959,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k3_tarski(k2_tarski(k1_xboole_0,X1))),k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_528]),
    [final]).

cnf(c_0_960,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)),X3),k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_528]),
    [final]).

cnf(c_0_961,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k3_tarski(k2_tarski(X1,k1_xboole_0))),k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_276]),
    [final]).

cnf(c_0_962,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)),X3),k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_276]),
    [final]).

cnf(c_0_963,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k4_subset_1(X2,X3,k3_tarski(k2_tarski(k1_xboole_0,X1))))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_529,c_0_52]),
    [final]).

cnf(c_0_964,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)),X3))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_529,c_0_39]),
    [final]).

cnf(c_0_965,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k4_subset_1(X2,X3,k3_tarski(k2_tarski(X1,k1_xboole_0))))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_267]),
    [final]).

cnf(c_0_966,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0))) = X1
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)),X3))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_267]),
    [final]).

cnf(c_0_967,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_254,c_0_127]),
    [final]).

cnf(c_0_968,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_179,c_0_127]),
    [final]).

cnf(c_0_969,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,k4_subset_1(X2,X3,X3))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_185,c_0_141]),
    [final]).

cnf(c_0_970,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4) = k5_xboole_0(k4_subset_1(X2,X3,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X4)
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X3),X3) ),
    inference(spm,[status(thm)],[c_0_256,c_0_141]),
    [final]).

cnf(c_0_971,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_530,c_0_52]),
    [final]).

cnf(c_0_972,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_530,c_0_39]),
    [final]).

cnf(c_0_973,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_531,c_0_532]),
    [final]).

cnf(c_0_974,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_533,c_0_52]),
    [final]).

cnf(c_0_975,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_533,c_0_39]),
    [final]).

cnf(c_0_976,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_534,c_0_52]),
    [final]).

cnf(c_0_977,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_534,c_0_39]),
    [final]).

cnf(c_0_978,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_535,c_0_113]),
    [final]).

cnf(c_0_979,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_536,c_0_52]),
    [final]).

cnf(c_0_980,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_536,c_0_39]),
    [final]).

cnf(c_0_981,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_537,c_0_532]),
    [final]).

cnf(c_0_982,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_538,c_0_39]),
    [final]).

cnf(c_0_983,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_539,c_0_39]),
    [final]).

cnf(c_0_984,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_540,c_0_39]),
    [final]).

cnf(c_0_985,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_541,c_0_39]),
    [final]).

cnf(c_0_986,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_505,c_0_38]),
    [final]).

cnf(c_0_987,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_505,c_0_32]),
    [final]).

cnf(c_0_988,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_213]),
    [final]).

cnf(c_0_989,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_286,c_0_213]),
    [final]).

cnf(c_0_990,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_286,c_0_214]),
    [final]).

cnf(c_0_991,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_272,c_0_38]),
    [final]).

cnf(c_0_992,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_272,c_0_32]),
    [final]).

cnf(c_0_993,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_542,c_0_39]),
    [final]).

cnf(c_0_994,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_506,c_0_38]),
    [final]).

cnf(c_0_995,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_506,c_0_32]),
    [final]).

cnf(c_0_996,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_543,c_0_113]),
    [final]).

cnf(c_0_997,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_544,c_0_52]),
    [final]).

cnf(c_0_998,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_544,c_0_39]),
    [final]).

cnf(c_0_999,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_545,c_0_52]),
    [final]).

cnf(c_0_1000,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_545,c_0_39]),
    [final]).

cnf(c_0_1001,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_546,c_0_52]),
    [final]).

cnf(c_0_1002,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_546,c_0_39]),
    [final]).

cnf(c_0_1003,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_547,c_0_52]),
    [final]).

cnf(c_0_1004,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_547,c_0_39]),
    [final]).

cnf(c_0_1005,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_548,c_0_53]),c_0_100])]),
    [final]).

cnf(c_0_1006,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_219]),c_0_41])]),
    [final]).

cnf(c_0_1007,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = k5_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_219]),c_0_41])]),
    [final]).

cnf(c_0_1008,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_549,c_0_39]),
    [final]).

cnf(c_0_1009,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_507,c_0_38]),
    [final]).

cnf(c_0_1010,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_507,c_0_32]),
    [final]).

cnf(c_0_1011,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_509,c_0_38]),
    [final]).

cnf(c_0_1012,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_509,c_0_32]),
    [final]).

cnf(c_0_1013,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_511,c_0_38]),
    [final]).

cnf(c_0_1014,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_511,c_0_32]),
    [final]).

cnf(c_0_1015,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_212,c_0_38]),
    [final]).

cnf(c_0_1016,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_212,c_0_32]),
    [final]).

cnf(c_0_1017,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_286,c_0_38]),
    [final]).

cnf(c_0_1018,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_286,c_0_32]),
    [final]).

cnf(c_0_1019,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_286,c_0_38]),
    [final]).

cnf(c_0_1020,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_286,c_0_32]),
    [final]).

cnf(c_0_1021,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_512,c_0_38]),
    [final]).

cnf(c_0_1022,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_512,c_0_32]),
    [final]).

cnf(c_0_1023,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_216,c_0_38]),
    [final]).

cnf(c_0_1024,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_216,c_0_32]),
    [final]).

cnf(c_0_1025,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_201,c_0_550]),
    [final]).

cnf(c_0_1026,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_286,c_0_550]),
    [final]).

cnf(c_0_1027,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_203,c_0_550]),
    [final]).

cnf(c_0_1028,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_550]),
    [final]).

cnf(c_0_1029,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_212,c_0_550]),
    [final]).

cnf(c_0_1030,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_202,c_0_550]),
    [final]).

cnf(c_0_1031,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_286,c_0_550]),
    [final]).

cnf(c_0_1032,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X3)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_216,c_0_550]),
    [final]).

cnf(c_0_1033,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_551,c_0_41]),
    [final]).

cnf(c_0_1034,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0)))) = k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_552,c_0_41]),
    [final]).

cnf(c_0_1035,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2)))) = k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2) ),
    inference(spm,[status(thm)],[c_0_553,c_0_41]),
    [final]).

cnf(c_0_1036,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_554,c_0_52]),
    [final]).

cnf(c_0_1037,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_554,c_0_39]),
    [final]).

cnf(c_0_1038,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_555,c_0_52]),
    [final]).

cnf(c_0_1039,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_555,c_0_39]),
    [final]).

cnf(c_0_1040,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_556,c_0_52]),
    [final]).

cnf(c_0_1041,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_556,c_0_39]),
    [final]).

cnf(c_0_1042,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_557,c_0_52]),
    [final]).

cnf(c_0_1043,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_557,c_0_39]),
    [final]).

cnf(c_0_1044,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_558,c_0_52]),
    [final]).

cnf(c_0_1045,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_558,c_0_39]),
    [final]).

cnf(c_0_1046,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_559,c_0_52]),
    [final]).

cnf(c_0_1047,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_559,c_0_39]),
    [final]).

cnf(c_0_1048,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_560,c_0_52]),
    [final]).

cnf(c_0_1049,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_560,c_0_39]),
    [final]).

cnf(c_0_1050,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_561,c_0_52]),
    [final]).

cnf(c_0_1051,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_561,c_0_39]),
    [final]).

cnf(c_0_1052,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_562,c_0_41]),
    [final]).

cnf(c_0_1053,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_563,c_0_41]),
    [final]).

cnf(c_0_1054,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_564,c_0_41]),
    [final]).

cnf(c_0_1055,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_565,c_0_41]),
    [final]).

cnf(c_0_1056,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_566,c_0_41]),
    [final]).

cnf(c_0_1057,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_567,c_0_41]),
    [final]).

cnf(c_0_1058,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_568,c_0_41]),
    [final]).

cnf(c_0_1059,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_569,c_0_41]),
    [final]).

cnf(c_0_1060,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_570,c_0_28]),
    [final]).

cnf(c_0_1061,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_571,c_0_28]),
    [final]).

cnf(c_0_1062,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_572,c_0_41]),
    [final]).

cnf(c_0_1063,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2))))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_573,c_0_41]),
    [final]).

cnf(c_0_1064,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_574,c_0_41]),
    [final]).

cnf(c_0_1065,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_575,c_0_41]),
    [final]).

cnf(c_0_1066,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_576,c_0_41]),
    [final]).

cnf(c_0_1067,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_577,c_0_41]),
    [final]).

cnf(c_0_1068,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2)))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_578,c_0_41]),
    [final]).

cnf(c_0_1069,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_579,c_0_41]),
    [final]).

cnf(c_0_1070,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_580,c_0_41]),
    [final]).

cnf(c_0_1071,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_581,c_0_41]),
    [final]).

cnf(c_0_1072,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0)))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_582,c_0_41]),
    [final]).

cnf(c_0_1073,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3))) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_583,c_0_41]),
    [final]).

cnf(c_0_1074,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_523]),c_0_41])]),
    [final]).

cnf(c_0_1075,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_523]),c_0_41])]),
    [final]).

cnf(c_0_1076,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_524]),c_0_41])]),
    [final]).

cnf(c_0_1077,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_524]),c_0_41])]),
    [final]).

cnf(c_0_1078,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_525]),c_0_41])]),
    [final]).

cnf(c_0_1079,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_525]),c_0_41])]),
    [final]).

cnf(c_0_1080,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_526]),c_0_41])]),
    [final]).

cnf(c_0_1081,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_526]),c_0_41])]),
    [final]).

cnf(c_0_1082,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))),k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_584,c_0_52]),
    [final]).

cnf(c_0_1083,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))),k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_584,c_0_39]),
    [final]).

cnf(c_0_1084,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_585,c_0_52]),
    [final]).

cnf(c_0_1085,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0)) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_585,c_0_39]),
    [final]).

cnf(c_0_1086,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_519]),c_0_41])]),
    [final]).

cnf(c_0_1087,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_519]),c_0_41])]),
    [final]).

cnf(c_0_1088,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_520]),c_0_41])]),
    [final]).

cnf(c_0_1089,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_520]),c_0_41])]),
    [final]).

cnf(c_0_1090,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_521]),c_0_41])]),
    [final]).

cnf(c_0_1091,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_521]),c_0_41])]),
    [final]).

cnf(c_0_1092,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_522]),c_0_41])]),
    [final]).

cnf(c_0_1093,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_522]),c_0_41])]),
    [final]).

cnf(c_0_1094,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_519,c_0_189]),c_0_76])]),
    [final]).

cnf(c_0_1095,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X1,X2))
    | ~ r1_xboole_0(X2,k4_subset_1(X3,X1,X2))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_586,c_0_52]),
    [final]).

cnf(c_0_1096,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X2,X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X3,X2,X1))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_586,c_0_39]),
    [final]).

cnf(c_0_1097,plain,
    ( X1 = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_586,c_0_28]),
    [final]).

cnf(c_0_1098,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_374,c_0_189]),c_0_80])]),
    [final]).

cnf(c_0_1099,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_520,c_0_189]),c_0_76])]),
    [final]).

cnf(c_0_1100,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_587,c_0_41]),
    [final]).

cnf(c_0_1101,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_375,c_0_189]),c_0_80])]),
    [final]).

cnf(c_0_1102,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_521,c_0_189]),c_0_76])]),
    [final]).

cnf(c_0_1103,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X1,X2),X1)
    | ~ r1_xboole_0(X2,k4_subset_1(X3,X1,X2))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_588,c_0_52]),
    [final]).

cnf(c_0_1104,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X2,X1),X1)
    | ~ r1_xboole_0(X2,k4_subset_1(X3,X2,X1))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_588,c_0_39]),
    [final]).

cnf(c_0_1105,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_588,c_0_28]),
    [final]).

cnf(c_0_1106,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk3_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_376,c_0_189]),c_0_80])]),
    [final]).

cnf(c_0_1107,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_522,c_0_189]),c_0_76])]),
    [final]).

cnf(c_0_1108,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X1,X2),X1)
    | ~ r1_xboole_0(k4_subset_1(X3,X1,X2),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_589,c_0_52]),
    [final]).

cnf(c_0_1109,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X2,X1),X1)
    | ~ r1_xboole_0(k4_subset_1(X3,X2,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_589,c_0_39]),
    [final]).

cnf(c_0_1110,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_589,c_0_28]),
    [final]).

cnf(c_0_1111,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_377,c_0_189]),c_0_80])]),
    [final]).

cnf(c_0_1112,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))),k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_528,c_0_38]),
    [final]).

cnf(c_0_1113,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)),k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_528,c_0_32]),
    [final]).

cnf(c_0_1114,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1))))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_590,c_0_41]),
    [final]).

cnf(c_0_1115,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0))))) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_591,c_0_41]),
    [final]).

cnf(c_0_1116,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1))))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_592,c_0_41]),
    [final]).

cnf(c_0_1117,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_593,c_0_41]),
    [final]).

cnf(c_0_1118,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0))))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_594,c_0_41]),
    [final]).

cnf(c_0_1119,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1))) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_585,c_0_28]),
    [final]).

cnf(c_0_1120,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_127]),
    [final]).

cnf(c_0_1121,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_141]),
    [final]).

cnf(c_0_1122,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_595,c_0_41]),
    [final]).

cnf(c_0_1123,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_596,c_0_41]),
    [final]).

cnf(c_0_1124,plain,
    ( k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_597,c_0_41]),
    [final]).

cnf(c_0_1125,plain,
    ( k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_598,c_0_41]),
    [final]).

cnf(c_0_1126,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_599,c_0_41]),
    [final]).

cnf(c_0_1127,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_600,c_0_41]),
    [final]).

cnf(c_0_1128,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_601,c_0_41]),
    [final]).

cnf(c_0_1129,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_387,c_0_41]),
    [final]).

cnf(c_0_1130,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_602]),
    [final]).

cnf(c_0_1131,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_602]),
    [final]).

cnf(c_0_1132,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_603]),
    [final]).

cnf(c_0_1133,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_603]),
    [final]).

cnf(c_0_1134,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_602,c_0_38]),
    [final]).

cnf(c_0_1135,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_602,c_0_32]),
    [final]).

cnf(c_0_1136,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_603,c_0_38]),
    [final]).

cnf(c_0_1137,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_603,c_0_32]),
    [final]).

cnf(c_0_1138,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,X1),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_201]),
    [final]).

cnf(c_0_1139,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X1,X3),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_201]),
    [final]).

cnf(c_0_1140,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_604,c_0_426]),c_0_226]),c_0_227]),
    [final]).

cnf(c_0_1141,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_604,c_0_428]),c_0_228]),c_0_229]),
    [final]).

cnf(c_0_1142,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_201,c_0_38]),
    [final]).

cnf(c_0_1143,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_201,c_0_32]),
    [final]).

cnf(c_0_1144,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,X1),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_605]),
    [final]).

cnf(c_0_1145,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X1,X3),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_605]),
    [final]).

cnf(c_0_1146,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_605,c_0_38]),
    [final]).

cnf(c_0_1147,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_605,c_0_32]),
    [final]).

cnf(c_0_1148,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_606]),
    [final]).

cnf(c_0_1149,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_606]),
    [final]).

cnf(c_0_1150,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_607]),
    [final]).

cnf(c_0_1151,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_607]),
    [final]).

cnf(c_0_1152,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_608]),
    [final]).

cnf(c_0_1153,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_608]),
    [final]).

cnf(c_0_1154,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_609]),
    [final]).

cnf(c_0_1155,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_609]),
    [final]).

cnf(c_0_1156,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_606,c_0_38]),
    [final]).

cnf(c_0_1157,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_606,c_0_32]),
    [final]).

cnf(c_0_1158,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_607,c_0_38]),
    [final]).

cnf(c_0_1159,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_607,c_0_32]),
    [final]).

cnf(c_0_1160,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_608,c_0_38]),
    [final]).

cnf(c_0_1161,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_608,c_0_32]),
    [final]).

cnf(c_0_1162,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_609,c_0_38]),
    [final]).

cnf(c_0_1163,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_609,c_0_32]),
    [final]).

cnf(c_0_1164,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X4,X1))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_202]),
    [final]).

cnf(c_0_1165,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k4_subset_1(X4,X1,X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_202]),
    [final]).

cnf(c_0_1166,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_202,c_0_38]),
    [final]).

cnf(c_0_1167,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_202,c_0_32]),
    [final]).

cnf(c_0_1168,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_610,c_0_611]),
    [final]).

cnf(c_0_1169,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_612,c_0_613]),
    [final]).

cnf(c_0_1170,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,X1),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_203]),
    [final]).

cnf(c_0_1171,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X1,X3),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_203]),
    [final]).

cnf(c_0_1172,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_203,c_0_38]),
    [final]).

cnf(c_0_1173,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_203,c_0_32]),
    [final]).

cnf(c_0_1174,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X4,X1),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_169]),
    [final]).

cnf(c_0_1175,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(k4_subset_1(X4,X1,X3),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_169]),
    [final]).

cnf(c_0_1176,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X4,X1))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_456,c_0_169]),
    [final]).

cnf(c_0_1177,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k4_subset_1(X4,X1,X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_457,c_0_169]),
    [final]).

cnf(c_0_1178,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_169,c_0_38]),
    [final]).

cnf(c_0_1179,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_169,c_0_32]),
    [final]).

cnf(c_0_1180,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_169,c_0_38]),
    [final]).

cnf(c_0_1181,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_169,c_0_32]),
    [final]).

cnf(c_0_1182,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_614,c_0_611]),
    [final]).

cnf(c_0_1183,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_615,c_0_613]),
    [final]).

cnf(c_0_1184,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_395]),
    [final]).

cnf(c_0_1185,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_395]),
    [final]).

cnf(c_0_1186,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_396]),
    [final]).

cnf(c_0_1187,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_396]),
    [final]).

cnf(c_0_1188,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_395,c_0_38]),
    [final]).

cnf(c_0_1189,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_395,c_0_32]),
    [final]).

cnf(c_0_1190,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_396,c_0_38]),
    [final]).

cnf(c_0_1191,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_396,c_0_32]),
    [final]).

cnf(c_0_1192,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X4,X1))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_154]),
    [final]).

cnf(c_0_1193,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k4_subset_1(X4,X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_154]),
    [final]).

cnf(c_0_1194,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_616,c_0_611]),c_0_226]),c_0_227]),
    [final]).

cnf(c_0_1195,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_616,c_0_613]),c_0_228]),c_0_229]),
    [final]).

cnf(c_0_1196,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_38]),
    [final]).

cnf(c_0_1197,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_32]),
    [final]).

cnf(c_0_1198,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X4,X1))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_617]),
    [final]).

cnf(c_0_1199,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,k4_subset_1(X4,X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_617]),
    [final]).

cnf(c_0_1200,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_617,c_0_38]),
    [final]).

cnf(c_0_1201,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k5_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_617,c_0_32]),
    [final]).

cnf(c_0_1202,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_618,c_0_426]),c_0_28]),c_0_226]),
    [final]).

cnf(c_0_1203,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_149,c_0_619]),
    [final]).

cnf(c_0_1204,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X1
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_619]),
    [final]).

cnf(c_0_1205,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_224,c_0_283]),
    [final]).

cnf(c_0_1206,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_283]),
    [final]).

cnf(c_0_1207,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_283]),
    [final]).

cnf(c_0_1208,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_620,c_0_28]),
    [final]).

cnf(c_0_1209,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_621,c_0_28]),
    [final]).

cnf(c_0_1210,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_622,c_0_426]),
    [final]).

cnf(c_0_1211,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_623,c_0_28]),
    [final]).

cnf(c_0_1212,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_624,c_0_428]),c_0_28]),c_0_228]),
    [final]).

cnf(c_0_1213,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_284]),
    [final]).

cnf(c_0_1214,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_284]),
    [final]).

cnf(c_0_1215,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_625,c_0_613]),c_0_28]),c_0_228]),
    [final]).

cnf(c_0_1216,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_626]),
    [final]).

cnf(c_0_1217,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_127]),
    [final]).

cnf(c_0_1218,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_127]),
    [final]).

cnf(c_0_1219,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_627]),
    [final]).

cnf(c_0_1220,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_628,c_0_52]),
    [final]).

cnf(c_0_1221,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_628,c_0_39]),
    [final]).

cnf(c_0_1222,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(esk2_0,X2)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_629,c_0_426]),c_0_28]),c_0_226]),
    [final]).

cnf(c_0_1223,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_630,c_0_611]),
    [final]).

cnf(c_0_1224,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X2
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_628,c_0_28]),
    [final]).

cnf(c_0_1225,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_631,c_0_428]),c_0_28]),c_0_228]),
    [final]).

cnf(c_0_1226,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_632,c_0_426]),
    [final]).

cnf(c_0_1227,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X2
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_149,c_0_633]),
    [final]).

cnf(c_0_1228,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_633]),
    [final]).

cnf(c_0_1229,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_400,c_0_28]),
    [final]).

cnf(c_0_1230,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_116,c_0_290]),
    [final]).

cnf(c_0_1231,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_290]),
    [final]).

cnf(c_0_1232,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_290]),
    [final]).

cnf(c_0_1233,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_634,c_0_611]),
    [final]).

cnf(c_0_1234,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_635,c_0_28]),
    [final]).

cnf(c_0_1235,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_224]),
    [final]).

cnf(c_0_1236,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_141]),
    [final]).

cnf(c_0_1237,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_141]),
    [final]).

cnf(c_0_1238,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,X2),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_151]),
    [final]).

cnf(c_0_1239,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X5,X2,X4),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_151]),
    [final]).

cnf(c_0_1240,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,X2)),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_151,c_0_38]),
    [final]).

cnf(c_0_1241,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X4)),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_151,c_0_32]),
    [final]).

cnf(c_0_1242,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_636]),
    [final]).

cnf(c_0_1243,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,esk2_0,X3),esk2_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_636]),
    [final]).

cnf(c_0_1244,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,k4_subset_1(X2,X3,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_410]),
    [final]).

cnf(c_0_1245,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,k4_subset_1(X2,esk2_0,X3)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_410]),
    [final]).

cnf(c_0_1246,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_637,c_0_41]),
    [final]).

cnf(c_0_1247,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_636,c_0_38]),
    [final]).

cnf(c_0_1248,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(esk2_0,X2)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_636,c_0_32]),
    [final]).

cnf(c_0_1249,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_636,c_0_226]),
    [final]).

cnf(c_0_1250,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_410,c_0_28]),
    [final]).

cnf(c_0_1251,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k3_tarski(k2_tarski(X2,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_410,c_0_38]),
    [final]).

cnf(c_0_1252,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k3_tarski(k2_tarski(esk2_0,X2))) ),
    inference(spm,[status(thm)],[c_0_410,c_0_32]),
    [final]).

cnf(c_0_1253,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_638,c_0_426]),
    [final]).

cnf(c_0_1254,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_639]),
    [final]).

cnf(c_0_1255,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3) = k1_xboole_0
    | ~ m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_639]),
    [final]).

cnf(c_0_1256,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_611]),c_0_28]),c_0_226]),
    [final]).

cnf(c_0_1257,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_407,c_0_28]),
    [final]).

cnf(c_0_1258,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(X2,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_640,c_0_428]),c_0_228]),
    [final]).

cnf(c_0_1259,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_641,c_0_28]),
    [final]).

cnf(c_0_1260,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X4,X5,X2))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_456,c_0_81]),
    [final]).

cnf(c_0_1261,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X5,X2,X4))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_457,c_0_81]),
    [final]).

cnf(c_0_1262,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X4,X2)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_38]),
    [final]).

cnf(c_0_1263,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_32]),
    [final]).

cnf(c_0_1264,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_642]),
    [final]).

cnf(c_0_1265,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,esk3_0,X3),esk3_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_642]),
    [final]).

cnf(c_0_1266,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_643,c_0_41]),
    [final]).

cnf(c_0_1267,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_642,c_0_38]),
    [final]).

cnf(c_0_1268,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(esk3_0,X2)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_642,c_0_32]),
    [final]).

cnf(c_0_1269,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_642,c_0_228]),
    [final]).

cnf(c_0_1270,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,k4_subset_1(X2,X3,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_120]),
    [final]).

cnf(c_0_1271,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,k4_subset_1(X2,esk3_0,X3)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_120]),
    [final]).

cnf(c_0_1272,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_120,c_0_28]),
    [final]).

cnf(c_0_1273,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k4_subset_1(X1,X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_456,c_0_644]),
    [final]).

cnf(c_0_1274,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k4_subset_1(X1,esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_457,c_0_644]),
    [final]).

cnf(c_0_1275,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_234]),
    [final]).

cnf(c_0_1276,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,k3_tarski(k2_tarski(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_644,c_0_38]),
    [final]).

cnf(c_0_1277,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,k3_tarski(k2_tarski(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_644,c_0_32]),
    [final]).

cnf(c_0_1278,negated_conjecture,
    ( k7_subset_1(esk3_0,esk3_0,k2_struct_0(esk1_0)) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_645,c_0_428]),
    [final]).

cnf(c_0_1279,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,k2_struct_0(esk1_0)) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_439,c_0_428]),
    [final]).

cnf(c_0_1280,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_163]),
    [final]).

cnf(c_0_1281,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_646,c_0_41]),
    [final]).

cnf(c_0_1282,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_456,c_0_163]),
    [final]).

cnf(c_0_1283,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,esk3_0,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_457,c_0_163]),
    [final]).

cnf(c_0_1284,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_28]),
    [final]).

cnf(c_0_1285,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_38]),
    [final]).

cnf(c_0_1286,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(esk3_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_32]),
    [final]).

cnf(c_0_1287,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_647,c_0_234]),
    [final]).

cnf(c_0_1288,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k7_subset_1(esk3_0,esk3_0,esk2_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_648,c_0_613]),
    [final]).

cnf(c_0_1289,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k3_tarski(k2_tarski(X2,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_38]),
    [final]).

cnf(c_0_1290,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k3_tarski(k2_tarski(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_32]),
    [final]).

cnf(c_0_1291,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk2_0) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_649,c_0_428]),
    [final]).

cnf(c_0_1292,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X4,X5,X2),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_456,c_0_135]),
    [final]).

cnf(c_0_1293,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X5,X2,X4),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_457,c_0_135]),
    [final]).

cnf(c_0_1294,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_416,c_0_28]),
    [final]).

cnf(c_0_1295,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_650,c_0_613]),
    [final]).

cnf(c_0_1296,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_417,c_0_28]),
    [final]).

cnf(c_0_1297,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_651,c_0_428]),
    [final]).

cnf(c_0_1298,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X4,X2)),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_135,c_0_38]),
    [final]).

cnf(c_0_1299,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X4)),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_135,c_0_32]),
    [final]).

cnf(c_0_1300,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X4,X5,X2))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_456,c_0_124]),
    [final]).

cnf(c_0_1301,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X5,X2,X4))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_457,c_0_124]),
    [final]).

cnf(c_0_1302,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X4,X2)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_124,c_0_38]),
    [final]).

cnf(c_0_1303,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_124,c_0_32]),
    [final]).

cnf(c_0_1304,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_226]),
    [final]).

cnf(c_0_1305,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_231,c_0_228]),
    [final]).

cnf(c_0_1306,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_652,c_0_426]),
    [final]).

cnf(c_0_1307,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_168,c_0_118]),
    [final]).

cnf(c_0_1308,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_653,c_0_428]),
    [final]).

cnf(c_0_1309,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_117]),
    [final]).

cnf(c_0_1310,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_654,c_0_426]),
    [final]).

cnf(c_0_1311,plain,
    ( k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_168,c_0_126]),
    [final]).

cnf(c_0_1312,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_655,c_0_428]),
    [final]).

cnf(c_0_1313,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2) = X2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_47]),
    [final]).

cnf(c_0_1314,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_656,c_0_426]),
    [final]).

cnf(c_0_1315,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_424,c_0_226]),
    [final]).

cnf(c_0_1316,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_657,c_0_428]),
    [final]).

cnf(c_0_1317,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_228]),
    [final]).

cnf(c_0_1318,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_658]),
    [final]).

cnf(c_0_1319,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k5_xboole_0(esk2_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_659,c_0_426]),
    [final]).

cnf(c_0_1320,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_660]),
    [final]).

cnf(c_0_1321,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k5_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_661,c_0_428]),
    [final]).

cnf(c_0_1322,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_118]),
    [final]).

cnf(c_0_1323,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_117]),
    [final]).

cnf(c_0_1324,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_176,c_0_126]),
    [final]).

cnf(c_0_1325,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_47]),
    [final]).

cnf(c_0_1326,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1) = X1
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,X1)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_283]),
    [final]).

cnf(c_0_1327,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1) = X1
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,k1_xboole_0)))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_284]),
    [final]).

cnf(c_0_1328,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_290]),
    [final]).

cnf(c_0_1329,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_224]),
    [final]).

cnf(c_0_1330,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0) = X1
    | ~ r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_662,c_0_28]),
    [final]).

cnf(c_0_1331,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k4_subset_1(X1,X2,X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_176,c_0_117]),
    [final]).

cnf(c_0_1332,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0) = X1
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_663,c_0_28]),
    [final]).

cnf(c_0_1333,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X2),X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_176,c_0_47]),
    [final]).

cnf(c_0_1334,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_664,c_0_611]),
    [final]).

cnf(c_0_1335,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_665,c_0_613]),
    [final]).

cnf(c_0_1336,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_666,c_0_426]),
    [final]).

cnf(c_0_1337,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_667,c_0_613]),
    [final]).

cnf(c_0_1338,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_668,c_0_611]),
    [final]).

cnf(c_0_1339,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3)) ),
    inference(spm,[status(thm)],[c_0_669,c_0_611]),
    [final]).

cnf(c_0_1340,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_670,c_0_613]),
    [final]).

cnf(c_0_1341,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3)) ),
    inference(spm,[status(thm)],[c_0_671,c_0_613]),
    [final]).

cnf(c_0_1342,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_672,c_0_611]),
    [final]).

cnf(c_0_1343,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_673,c_0_611]),
    [final]).

cnf(c_0_1344,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_674,c_0_611]),
    [final]).

cnf(c_0_1345,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_675,c_0_611]),
    [final]).

cnf(c_0_1346,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_676,c_0_613]),
    [final]).

cnf(c_0_1347,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_677,c_0_613]),
    [final]).

cnf(c_0_1348,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0)))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_678,c_0_613]),
    [final]).

cnf(c_0_1349,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1))) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_679,c_0_613]),
    [final]).

cnf(c_0_1350,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k4_subset_1(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_162,c_0_42]),
    [final]).

cnf(c_0_1351,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(k4_subset_1(X3,X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_162,c_0_44]),
    [final]).

cnf(c_0_1352,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,k4_subset_1(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_42]),
    [final]).

cnf(c_0_1353,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_680,c_0_611]),
    [final]).

cnf(c_0_1354,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_681,c_0_611]),
    [final]).

cnf(c_0_1355,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X1,k4_subset_1(X3,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_44]),
    [final]).

cnf(c_0_1356,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_682,c_0_611]),
    [final]).

cnf(c_0_1357,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2))) ),
    inference(spm,[status(thm)],[c_0_683,c_0_611]),
    [final]).

cnf(c_0_1358,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_684,c_0_613]),
    [final]).

cnf(c_0_1359,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_685,c_0_613]),
    [final]).

cnf(c_0_1360,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_303]),
    [final]).

cnf(c_0_1361,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(X2,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_434]),
    [final]).

cnf(c_0_1362,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),X2) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_434]),
    [final]).

cnf(c_0_1363,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_686,c_0_613]),
    [final]).

cnf(c_0_1364,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_434,c_0_303]),
    [final]).

cnf(c_0_1365,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_687,c_0_611]),
    [final]).

cnf(c_0_1366,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_688,c_0_613]),
    [final]).

cnf(c_0_1367,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0)) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2))) ),
    inference(spm,[status(thm)],[c_0_689,c_0_613]),
    [final]).

cnf(c_0_1368,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_162,c_0_38]),
    [final]).

cnf(c_0_1369,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_162,c_0_32]),
    [final]).

cnf(c_0_1370,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_690,c_0_613]),
    [final]).

cnf(c_0_1371,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_38]),
    [final]).

cnf(c_0_1372,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_32]),
    [final]).

cnf(c_0_1373,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk2_0) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_691,c_0_226]),
    [final]).

cnf(c_0_1374,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk2_0) = k5_xboole_0(esk2_0,k1_xboole_0)
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_692,c_0_226]),
    [final]).

cnf(c_0_1375,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_693,c_0_613]),
    [final]).

cnf(c_0_1376,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0) = esk3_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_694,c_0_611]),
    [final]).

cnf(c_0_1377,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_695,c_0_253]),
    [final]).

cnf(c_0_1378,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,esk2_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_189,c_0_52]),
    [final]).

cnf(c_0_1379,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_696,c_0_128]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_1380,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_697,c_0_128]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_1381,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(esk3_0,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_698,c_0_128]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_1382,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_xboole_0(esk2_0,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_699,c_0_128]),c_0_68]),c_0_91])]),
    [final]).

cnf(c_0_1383,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_695,c_0_436]),
    [final]).

cnf(c_0_1384,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_700,c_0_56]),
    [final]).

cnf(c_0_1385,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0) = k7_subset_1(esk3_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_701,c_0_76]),
    [final]).

cnf(c_0_1386,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))) = k7_subset_1(esk3_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_234]),
    [final]).

cnf(c_0_1387,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.91/2.09  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.91/2.09  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.91/2.09  #
% 1.91/2.09  # Preprocessing time       : 0.027 s
% 1.91/2.09  # Presaturation interreduction done
% 1.91/2.09  
% 1.91/2.09  # No proof found!
% 1.91/2.09  # SZS status CounterSatisfiable
% 1.91/2.09  # SZS output start Saturation
% 1.91/2.09  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.91/2.09  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.91/2.09  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.91/2.09  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.91/2.09  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.91/2.09  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.91/2.09  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.91/2.09  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.91/2.09  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.91/2.09  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.91/2.09  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_pre_topc)).
% 1.91/2.09  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.91/2.09  fof(c_0_12, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.91/2.09  fof(c_0_13, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.91/2.09  fof(c_0_14, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k7_subset_1(X21,X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 1.91/2.09  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.91/2.09  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.91/2.09  fof(c_0_17, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.91/2.09  fof(c_0_18, plain, ![X8, X9]:k3_xboole_0(X8,k2_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 1.91/2.09  fof(c_0_19, plain, ![X14, X15]:k3_tarski(k2_tarski(X14,X15))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.91/2.09  cnf(c_0_20, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.91/2.09  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 1.91/2.09  fof(c_0_22, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.91/2.09  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.91/2.09  cnf(c_0_24, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.91/2.09  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.91/2.09  fof(c_0_26, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|~m1_subset_1(X20,k1_zfmisc_1(X18))|k4_subset_1(X18,X19,X20)=k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.91/2.09  cnf(c_0_27, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 1.91/2.09  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 1.91/2.09  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_16]), ['final']).
% 1.91/2.09  fof(c_0_30, plain, ![X17]:m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 1.91/2.09  fof(c_0_31, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 1.91/2.09  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_16]), ['final']).
% 1.91/2.09  cnf(c_0_33, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.91/2.09  cnf(c_0_34, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_35, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_27, c_0_29]), ['final']).
% 1.91/2.09  cnf(c_0_36, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.91/2.09  cnf(c_0_37, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.91/2.09  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_32, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_39, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_25]), ['final']).
% 1.91/2.09  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.91/2.09  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_37]), ['final']).
% 1.91/2.09  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_44, plain, (k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))=X1|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.91/2.09  cnf(c_0_46, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_42]), ['final']).
% 1.91/2.09  cnf(c_0_47, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 1.91/2.09  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_16]), ['final']).
% 1.91/2.09  cnf(c_0_49, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_46, c_0_47]), ['final']).
% 1.91/2.09  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_51, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_49]), c_0_28])).
% 1.91/2.09  cnf(c_0_52, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_53, plain, (r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32])]), ['final']).
% 1.91/2.09  cnf(c_0_54, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_51, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_55, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_39, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_56, plain, (r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_57, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.91/2.09  cnf(c_0_58, plain, (r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_59, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_60, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.91/2.09  cnf(c_0_61, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_59]), ['final']).
% 1.91/2.09  fof(c_0_62, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 1.91/2.09  cnf(c_0_63, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_64, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X5)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X5,X2)), inference(spm,[status(thm)],[c_0_35, c_0_61]), ['final']).
% 1.91/2.09  fof(c_0_65, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).
% 1.91/2.09  cnf(c_0_66, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_63]), ['final']).
% 1.91/2.09  cnf(c_0_67, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_27, c_0_64])).
% 1.91/2.09  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.09  cnf(c_0_69, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_35, c_0_66]), ['final']).
% 1.91/2.09  cnf(c_0_70, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X3,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.91/2.09  cnf(c_0_71, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_69]), c_0_28])).
% 1.91/2.09  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_70])).
% 1.91/2.09  cnf(c_0_73, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_71, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_41])).
% 1.91/2.09  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_29]), ['final']).
% 1.91/2.09  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.09  cnf(c_0_77, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X4)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_64])).
% 1.91/2.09  cnf(c_0_78, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_27, c_0_73])).
% 1.91/2.09  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X3,esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_74])).
% 1.91/2.09  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_75, c_0_76]), ['final']).
% 1.91/2.09  cnf(c_0_81, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X4)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_77, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_82, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_78, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_83, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 1.91/2.09  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_28])).
% 1.91/2.09  cnf(c_0_85, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.91/2.09  cnf(c_0_86, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X5)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X5,X2)), inference(spm,[status(thm)],[c_0_61, c_0_61]), ['final']).
% 1.91/2.09  cnf(c_0_87, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_76])).
% 1.91/2.09  cnf(c_0_89, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_85, c_0_41])).
% 1.91/2.09  cnf(c_0_90, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_27, c_0_86])).
% 1.91/2.09  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.09  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))=k5_xboole_0(esk3_0,k1_xboole_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.91/2.09  cnf(c_0_93, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_89, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_94, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X3,esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 1.91/2.09  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))=k5_xboole_0(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_80])).
% 1.91/2.09  cnf(c_0_96, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_93]), ['final']).
% 1.91/2.09  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_94])).
% 1.91/2.09  cnf(c_0_98, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_xboole_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_95])).
% 1.91/2.09  cnf(c_0_99, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_96]), c_0_41])])).
% 1.91/2.09  cnf(c_0_100, plain, (r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X1)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_32])]), ['final']).
% 1.91/2.09  fof(c_0_101, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|k4_xboole_0(k2_xboole_0(X10,X11),X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 1.91/2.09  cnf(c_0_102, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_61])).
% 1.91/2.09  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_97, c_0_41])).
% 1.91/2.09  cnf(c_0_104, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k7_subset_1(X3,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_35, c_0_98]), ['final']).
% 1.91/2.09  cnf(c_0_105, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_99, c_0_41])).
% 1.91/2.09  cnf(c_0_106, plain, (r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_100, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_107, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.91/2.09  cnf(c_0_108, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X5)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X2,X5)), inference(spm,[status(thm)],[c_0_35, c_0_35]), ['final']).
% 1.91/2.09  cnf(c_0_109, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_102, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X3,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_103, c_0_103])).
% 1.91/2.09  cnf(c_0_111, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_104])).
% 1.91/2.09  cnf(c_0_112, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_58]), c_0_28])).
% 1.91/2.09  cnf(c_0_113, plain, (r1_xboole_0(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_106, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_114, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_25]), c_0_21])).
% 1.91/2.09  cnf(c_0_115, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X2,X4)), inference(spm,[status(thm)],[c_0_27, c_0_108])).
% 1.91/2.09  cnf(c_0_116, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_117, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_109, c_0_44]), ['final']).
% 1.91/2.09  cnf(c_0_118, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_109, c_0_42]), ['final']).
% 1.91/2.09  cnf(c_0_119, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_80]), c_0_28])).
% 1.91/2.09  cnf(c_0_120, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_111, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_121, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_112, c_0_113]), ['final']).
% 1.91/2.09  cnf(c_0_122, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_114, c_0_28])).
% 1.91/2.09  cnf(c_0_123, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_44]), ['final']).
% 1.91/2.09  cnf(c_0_124, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X2,X4)), inference(spm,[status(thm)],[c_0_115, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_125, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)=k7_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)), inference(spm,[status(thm)],[c_0_35, c_0_116]), ['final']).
% 1.91/2.09  cnf(c_0_126, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_43, c_0_42]), ['final']).
% 1.91/2.09  cnf(c_0_127, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_117, c_0_118]), ['final']).
% 1.91/2.09  cnf(c_0_128, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.09  cnf(c_0_129, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_39, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_130, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_119, c_0_80])).
% 1.91/2.09  cnf(c_0_131, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(X2,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,X3)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_120])).
% 1.91/2.09  cnf(c_0_132, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k7_subset_1(X5,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_35, c_0_46]), ['final']).
% 1.91/2.09  cnf(c_0_133, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_121]), ['final']).
% 1.91/2.09  cnf(c_0_134, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_122, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_135, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_67, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_136, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_34, c_0_64])).
% 1.91/2.09  cnf(c_0_137, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k7_subset_1(X5,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_35, c_0_123]), ['final']).
% 1.91/2.09  cnf(c_0_138, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_124])).
% 1.91/2.09  cnf(c_0_139, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)), inference(spm,[status(thm)],[c_0_27, c_0_125])).
% 1.91/2.09  cnf(c_0_140, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_34, c_0_86])).
% 1.91/2.09  cnf(c_0_141, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_47, c_0_126]), ['final']).
% 1.91/2.09  cnf(c_0_142, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X2,X4)), inference(spm,[status(thm)],[c_0_34, c_0_108])).
% 1.91/2.09  cnf(c_0_143, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))), inference(spm,[status(thm)],[c_0_123, c_0_127]), ['final']).
% 1.91/2.09  cnf(c_0_144, negated_conjecture, (k4_subset_1(X1,esk2_0,esk3_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.09  cnf(c_0_145, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))=k5_xboole_0(esk2_0,k1_xboole_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_109, c_0_130])).
% 1.91/2.09  cnf(c_0_146, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_61])).
% 1.91/2.09  cnf(c_0_147, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_131, c_0_41])).
% 1.91/2.09  cnf(c_0_148, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 1.91/2.09  cnf(c_0_149, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X2|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_134, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_150, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_135])).
% 1.91/2.09  cnf(c_0_151, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_90, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_152, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_136, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_153, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_27, c_0_137])).
% 1.91/2.09  cnf(c_0_154, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_138, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_155, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)), inference(spm,[status(thm)],[c_0_139, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_156, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_140, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_157, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_123, c_0_141]), ['final']).
% 1.91/2.09  cnf(c_0_158, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)|~r1_xboole_0(X2,X4)), inference(spm,[status(thm)],[c_0_142, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_159, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))), inference(spm,[status(thm)],[c_0_64, c_0_143])).
% 1.91/2.09  cnf(c_0_160, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_144])).
% 1.91/2.09  cnf(c_0_161, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))=k5_xboole_0(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_145, c_0_80]), ['final']).
% 1.91/2.09  cnf(c_0_162, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_146, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_163, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_147, c_0_80]), ['final']).
% 1.91/2.09  cnf(c_0_164, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_148, c_0_41])).
% 1.91/2.09  cnf(c_0_165, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k7_subset_1(X5,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_46]), ['final']).
% 1.91/2.09  cnf(c_0_166, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k7_subset_1(X5,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_61, c_0_123]), ['final']).
% 1.91/2.09  cnf(c_0_167, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)=k7_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_116]), ['final']).
% 1.91/2.09  cnf(c_0_168, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_149, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_169, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_150, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_170, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_151])).
% 1.91/2.09  cnf(c_0_171, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_152])).
% 1.91/2.09  cnf(c_0_172, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_135])).
% 1.91/2.09  cnf(c_0_173, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_153, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_174, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X4)), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 1.91/2.09  cnf(c_0_175, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_176, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_134, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_177, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_134, c_0_35]), ['final']).
% 1.91/2.09  cnf(c_0_178, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_61, c_0_118]), ['final']).
% 1.91/2.09  cnf(c_0_179, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_61, c_0_117]), ['final']).
% 1.91/2.09  cnf(c_0_180, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X4)), inference(spm,[status(thm)],[c_0_61, c_0_126]), ['final']).
% 1.91/2.09  cnf(c_0_181, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_156])).
% 1.91/2.09  cnf(c_0_182, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_143]), c_0_28])).
% 1.91/2.09  cnf(c_0_183, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_157]), c_0_28])).
% 1.91/2.09  cnf(c_0_184, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_158])).
% 1.91/2.09  cnf(c_0_185, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X3)), inference(spm,[status(thm)],[c_0_61, c_0_47]), ['final']).
% 1.91/2.09  cnf(c_0_186, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_134, c_0_61]), ['final']).
% 1.91/2.09  cnf(c_0_187, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_159, c_0_41])).
% 1.91/2.09  cnf(c_0_188, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_149, c_0_116]), ['final']).
% 1.91/2.09  cnf(c_0_189, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_68]), c_0_91])]), ['final']).
% 1.91/2.09  cnf(c_0_190, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_161]), ['final']).
% 1.91/2.09  cnf(c_0_191, negated_conjecture, (k5_xboole_0(esk3_0,k1_xboole_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 1.91/2.09  cnf(c_0_192, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_164, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_193, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_165]), c_0_28])).
% 1.91/2.09  cnf(c_0_194, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_132]), c_0_28])).
% 1.91/2.09  cnf(c_0_195, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_166]), c_0_28])).
% 1.91/2.09  cnf(c_0_196, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_137]), c_0_28])).
% 1.91/2.09  cnf(c_0_197, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_167])).
% 1.91/2.09  cnf(c_0_198, plain, (k7_subset_1(X1,X2,k3_tarski(k2_tarski(X2,X3)))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_199, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_168, c_0_123]), ['final']).
% 1.91/2.09  cnf(c_0_200, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_169, c_0_82])).
% 1.91/2.09  cnf(c_0_201, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_170, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_202, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_171, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_203, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_172, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_204, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_133, c_0_173])).
% 1.91/2.09  cnf(c_0_205, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X3)), inference(spm,[status(thm)],[c_0_174, c_0_41])).
% 1.91/2.09  cnf(c_0_206, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_134, c_0_175]), ['final']).
% 1.91/2.09  cnf(c_0_207, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_176, c_0_123]), ['final']).
% 1.91/2.09  cnf(c_0_208, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_177])).
% 1.91/2.09  cnf(c_0_209, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_176, c_0_178]), ['final']).
% 1.91/2.09  cnf(c_0_210, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_168, c_0_179]), ['final']).
% 1.91/2.09  cnf(c_0_211, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X4)|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_176, c_0_180]), ['final']).
% 1.91/2.09  cnf(c_0_212, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_181, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_213, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_182, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_214, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_183, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_215, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X4)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_64])).
% 1.91/2.09  cnf(c_0_216, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_184, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_217, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X4))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X3)|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_168, c_0_185]), ['final']).
% 1.91/2.09  cnf(c_0_218, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_186])).
% 1.91/2.09  cnf(c_0_219, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_187, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_220, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_188, c_0_86])).
% 1.91/2.09  cnf(c_0_221, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_188, c_0_64])).
% 1.91/2.09  cnf(c_0_222, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_188, c_0_64])).
% 1.91/2.09  cnf(c_0_223, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_188, c_0_108])).
% 1.91/2.09  cnf(c_0_224, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_225, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_152])).
% 1.91/2.09  cnf(c_0_226, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_struct_0(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_128]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.09  cnf(c_0_227, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),esk2_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_189]), c_0_80])]), ['final']).
% 1.91/2.09  cnf(c_0_228, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,k2_struct_0(esk1_0)))=esk3_0), inference(spm,[status(thm)],[c_0_38, c_0_189]), ['final']).
% 1.91/2.09  cnf(c_0_229, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_189]), c_0_76])]), ['final']).
% 1.91/2.09  cnf(c_0_230, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_124])).
% 1.91/2.09  cnf(c_0_231, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X3,esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_68])).
% 1.91/2.09  cnf(c_0_232, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_94])).
% 1.91/2.09  cnf(c_0_233, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k7_subset_1(X3,esk2_0,esk3_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_35, c_0_190]), ['final']).
% 1.91/2.09  cnf(c_0_234, negated_conjecture, (k5_xboole_0(esk3_0,k1_xboole_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_191, c_0_76]), ['final']).
% 1.91/2.09  cnf(c_0_235, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_192, c_0_192]), ['final']).
% 1.91/2.09  cnf(c_0_236, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_237, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_93]), ['final']).
% 1.91/2.09  cnf(c_0_238, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_193, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_239, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_194, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_240, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_195, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_241, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_196, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_242, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_197, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_243, plain, (k7_subset_1(X1,X2,k4_subset_1(X3,X4,X2))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_198, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_244, plain, (k7_subset_1(X1,X2,k4_subset_1(X3,X2,X4))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_27, c_0_44]), ['final']).
% 1.91/2.09  cnf(c_0_245, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_199]), c_0_28])).
% 1.91/2.09  cnf(c_0_246, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_200, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_247, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_201, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_248, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_202, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_249, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_203, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_250, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_154, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_251, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_204, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_252, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(X4,k4_subset_1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_35, c_0_118]), ['final']).
% 1.91/2.09  cnf(c_0_253, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_27, c_0_27]), ['final']).
% 1.91/2.09  cnf(c_0_254, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(X3,k4_subset_1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_35, c_0_117]), ['final']).
% 1.91/2.09  cnf(c_0_255, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(k4_subset_1(X2,X3,X4),X4)), inference(spm,[status(thm)],[c_0_35, c_0_126]), ['final']).
% 1.91/2.09  cnf(c_0_256, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(k4_subset_1(X2,X3,X4),X3)), inference(spm,[status(thm)],[c_0_35, c_0_47]), ['final']).
% 1.91/2.09  cnf(c_0_257, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_53]), c_0_32])).
% 1.91/2.09  cnf(c_0_258, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_206, c_0_86])).
% 1.91/2.09  cnf(c_0_259, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_206, c_0_64])).
% 1.91/2.09  cnf(c_0_260, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_206, c_0_64])).
% 1.91/2.09  cnf(c_0_261, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X5))|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_206, c_0_108])).
% 1.91/2.09  cnf(c_0_262, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_64, c_0_207])).
% 1.91/2.09  cnf(c_0_263, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_86, c_0_207])).
% 1.91/2.09  cnf(c_0_264, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_108, c_0_207])).
% 1.91/2.09  cnf(c_0_265, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_188, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_266, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_149, c_0_61]), ['final']).
% 1.91/2.09  cnf(c_0_267, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_208, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_268, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_209, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_269, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_210, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_270, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_211, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_271, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_212, c_0_213]), ['final']).
% 1.91/2.09  cnf(c_0_272, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_203, c_0_214]), ['final']).
% 1.91/2.09  cnf(c_0_273, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X4,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X4)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_215, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_274, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_216, c_0_214]), ['final']).
% 1.91/2.09  cnf(c_0_275, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_217, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_276, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_218, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_277, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=k7_subset_1(X3,k4_subset_1(X1,X2,X2),X4)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X5)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_219]), c_0_41])])).
% 1.91/2.09  cnf(c_0_278, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_219, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_279, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_220, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_280, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_221, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_281, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_222, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_282, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_223, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_283, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_109, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_284, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_109, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_285, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_175, c_0_224]), ['final']).
% 1.91/2.09  cnf(c_0_286, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_225, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_287, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_288, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_289, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_230, c_0_91])).
% 1.91/2.09  cnf(c_0_290, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_43, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_291, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_231])).
% 1.91/2.09  cnf(c_0_292, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_61, c_0_224]), ['final']).
% 1.91/2.09  cnf(c_0_293, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_232, c_0_41])).
% 1.91/2.09  cnf(c_0_294, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k7_subset_1(X3,esk2_0,esk3_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_190]), ['final']).
% 1.91/2.09  cnf(c_0_295, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_233])).
% 1.91/2.09  cnf(c_0_296, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_231])).
% 1.91/2.09  cnf(c_0_297, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k7_subset_1(X3,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_98]), ['final']).
% 1.91/2.09  cnf(c_0_298, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_98, c_0_234]), ['final']).
% 1.91/2.09  cnf(c_0_299, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X3)), inference(spm,[status(thm)],[c_0_115, c_0_91])).
% 1.91/2.09  cnf(c_0_300, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X3)), inference(spm,[status(thm)],[c_0_115, c_0_68])).
% 1.91/2.09  cnf(c_0_301, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_302, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_303, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_304, plain, (k1_xboole_0=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_32, c_0_59]), ['final']).
% 1.91/2.09  cnf(c_0_305, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_306, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X3,esk3_0)), inference(spm,[status(thm)],[c_0_135, c_0_163])).
% 1.91/2.09  cnf(c_0_307, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_235]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_308, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_309, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_310, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_237]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_311, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_238])).
% 1.91/2.09  cnf(c_0_312, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_27, c_0_239])).
% 1.91/2.09  cnf(c_0_313, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_27, c_0_240])).
% 1.91/2.09  cnf(c_0_314, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_241])).
% 1.91/2.09  cnf(c_0_315, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)),k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_242, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_316, plain, (k7_subset_1(X1,X2,k3_tarski(k2_tarski(X3,X2)))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_317, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)))), inference(spm,[status(thm)],[c_0_155, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_318, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_243])).
% 1.91/2.09  cnf(c_0_319, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_244])).
% 1.91/2.09  cnf(c_0_320, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_235]), c_0_41])])).
% 1.91/2.09  cnf(c_0_321, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_235]), c_0_41])])).
% 1.91/2.09  cnf(c_0_322, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_236]), c_0_41])])).
% 1.91/2.09  cnf(c_0_323, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_236]), c_0_41])])).
% 1.91/2.09  cnf(c_0_324, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_236]), c_0_41])])).
% 1.91/2.09  cnf(c_0_325, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_236]), c_0_41])])).
% 1.91/2.09  cnf(c_0_326, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_237]), c_0_41])])).
% 1.91/2.09  cnf(c_0_327, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_237]), c_0_41])])).
% 1.91/2.09  cnf(c_0_328, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_245, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_329, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_246, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_330, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_82, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_331, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_247, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_332, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_248, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_333, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_249, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_334, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_250, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_335, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_66]), ['final']).
% 1.91/2.09  cnf(c_0_336, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_169, c_0_251])).
% 1.91/2.09  cnf(c_0_337, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(X4,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_176, c_0_252]), ['final']).
% 1.91/2.09  cnf(c_0_338, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_339, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(X3,k4_subset_1(X2,X3,X4))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_168, c_0_254]), ['final']).
% 1.91/2.09  cnf(c_0_340, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(k4_subset_1(X2,X3,X4),X4)|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_176, c_0_255]), ['final']).
% 1.91/2.09  cnf(c_0_341, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X5)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X4),X5)|~r1_xboole_0(k4_subset_1(X2,X3,X4),X3)|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_168, c_0_256]), ['final']).
% 1.91/2.09  cnf(c_0_342, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_257, c_0_53]), ['final']).
% 1.91/2.09  cnf(c_0_343, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_123]), c_0_28])).
% 1.91/2.09  cnf(c_0_344, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)=k7_subset_1(X4,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_61, c_0_175]), ['final']).
% 1.91/2.09  cnf(c_0_345, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)=k7_subset_1(X4,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_35, c_0_175]), ['final']).
% 1.91/2.09  cnf(c_0_346, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_258, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_347, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_259, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_348, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_260, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_349, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_261, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_350, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_176, c_0_254]), ['final']).
% 1.91/2.09  cnf(c_0_351, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_262, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_352, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_263, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_353, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_264, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_354, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_265]), c_0_28])).
% 1.91/2.09  cnf(c_0_355, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_266])).
% 1.91/2.09  cnf(c_0_356, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_267, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_357, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X5,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_268]), c_0_41])])).
% 1.91/2.09  cnf(c_0_358, plain, (r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_359, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X5,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_269]), c_0_41])])).
% 1.91/2.09  cnf(c_0_360, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X5,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_270]), c_0_41])])).
% 1.91/2.09  cnf(c_0_361, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))), inference(spm,[status(thm)],[c_0_156, c_0_271])).
% 1.91/2.09  cnf(c_0_362, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X5,k4_subset_1(X2,X3,X3))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_151, c_0_272])).
% 1.91/2.09  cnf(c_0_363, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X5,k4_subset_1(X2,X3,X3))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_135, c_0_272])).
% 1.91/2.09  cnf(c_0_364, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X5)|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_273, c_0_274])).
% 1.91/2.09  cnf(c_0_365, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(k4_subset_1(X2,X3,X3),X5)|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_158, c_0_274])).
% 1.91/2.09  cnf(c_0_366, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X5,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_275]), c_0_41])])).
% 1.91/2.09  cnf(c_0_367, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)),k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_276, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_368, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_277, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_369, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_53]), c_0_100])])).
% 1.91/2.09  cnf(c_0_370, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_207]), c_0_28])).
% 1.91/2.09  cnf(c_0_371, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_123, c_0_118]), ['final']).
% 1.91/2.09  cnf(c_0_372, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_46, c_0_117]), ['final']).
% 1.91/2.09  cnf(c_0_373, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)), inference(spm,[status(thm)],[c_0_123, c_0_126]), ['final']).
% 1.91/2.09  cnf(c_0_374, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X2|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_279, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_375, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_280, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_376, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_281, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_377, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_282, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_378, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_135])).
% 1.91/2.09  cnf(c_0_379, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_135])).
% 1.91/2.09  cnf(c_0_380, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))|~r1_xboole_0(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_168]), ['final']).
% 1.91/2.09  cnf(c_0_381, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),X4)=X3|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)|~r1_xboole_0(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_168]), ['final']).
% 1.91/2.09  cnf(c_0_382, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))|~r1_xboole_0(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_176]), ['final']).
% 1.91/2.09  cnf(c_0_383, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)|~r1_xboole_0(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_176]), ['final']).
% 1.91/2.09  cnf(c_0_384, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_149, c_0_35]), ['final']).
% 1.91/2.09  cnf(c_0_385, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_116, c_0_283]), ['final']).
% 1.91/2.09  cnf(c_0_386, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_175, c_0_284]), ['final']).
% 1.91/2.09  cnf(c_0_387, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_149, c_0_285]), ['final']).
% 1.91/2.09  cnf(c_0_388, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_389, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_390, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_151])).
% 1.91/2.09  cnf(c_0_391, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_392, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_393, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_394, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_395, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_287, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_396, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_288, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_397, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_138, c_0_91])).
% 1.91/2.09  cnf(c_0_398, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_171, c_0_91])).
% 1.91/2.09  cnf(c_0_399, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_150, c_0_91])).
% 1.91/2.09  cnf(c_0_400, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_289, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_401, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_290, c_0_284]), ['final']).
% 1.91/2.09  cnf(c_0_402, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_138, c_0_68])).
% 1.91/2.09  cnf(c_0_403, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_28])).
% 1.91/2.09  cnf(c_0_404, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_291, c_0_41])).
% 1.91/2.09  cnf(c_0_405, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_28])).
% 1.91/2.09  cnf(c_0_406, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_292])).
% 1.91/2.09  cnf(c_0_407, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_293, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_408, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_230, c_0_68])).
% 1.91/2.09  cnf(c_0_409, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_294])).
% 1.91/2.09  cnf(c_0_410, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_295, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_411, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_123, c_0_207])).
% 1.91/2.09  cnf(c_0_412, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_296, c_0_41])).
% 1.91/2.09  cnf(c_0_413, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_297])).
% 1.91/2.09  cnf(c_0_414, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_298]), c_0_80])])).
% 1.91/2.09  cnf(c_0_415, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,k1_xboole_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_68])).
% 1.91/2.09  cnf(c_0_416, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_417, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_418, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X3)|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_77, c_0_91])).
% 1.91/2.09  cnf(c_0_419, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X3)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X3)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_68])).
% 1.91/2.09  cnf(c_0_420, negated_conjecture, (k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0))=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_421, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X3,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X3,esk2_0)), inference(spm,[status(thm)],[c_0_136, c_0_91])).
% 1.91/2.09  cnf(c_0_422, negated_conjecture, (k7_subset_1(X1,esk3_0,k2_struct_0(esk1_0))=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_423, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X3,esk3_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X3,esk3_0)), inference(spm,[status(thm)],[c_0_136, c_0_68])).
% 1.91/2.09  cnf(c_0_424, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X3)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X3,esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_91])).
% 1.91/2.09  cnf(c_0_425, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_299, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_426, negated_conjecture, (r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_427, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_300, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_428, negated_conjecture, (r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_429, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X2,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_301]), ['final']).
% 1.91/2.09  cnf(c_0_430, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X2,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_302]), ['final']).
% 1.91/2.09  cnf(c_0_431, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X2)), inference(spm,[status(thm)],[c_0_35, c_0_303]), ['final']).
% 1.91/2.09  cnf(c_0_432, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)), inference(spm,[status(thm)],[c_0_35, c_0_302]), ['final']).
% 1.91/2.09  cnf(c_0_433, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)), inference(spm,[status(thm)],[c_0_35, c_0_301]), ['final']).
% 1.91/2.09  cnf(c_0_434, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_435, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk3_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_228]), c_0_229]), ['final']).
% 1.91/2.09  cnf(c_0_436, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_226]), c_0_227]), ['final']).
% 1.91/2.09  cnf(c_0_437, plain, (k1_xboole_0=X1|~r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_304, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_438, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_305, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_439, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,X1)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_306, c_0_68]), ['final']).
% 1.91/2.09  cnf(c_0_440, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_307, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_441, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_308, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_442, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_309, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_443, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_310, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_444, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_311, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_445, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_312, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_446, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_313, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_447, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)), inference(spm,[status(thm)],[c_0_314, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_448, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)),k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_315, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_449, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_235]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_450, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_451, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_452, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_237]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_453, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)),k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_315, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_454, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))), inference(spm,[status(thm)],[c_0_317, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_455, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))), inference(spm,[status(thm)],[c_0_317, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_456, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_318, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_457, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_319, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_458, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)),k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_315, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_459, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_320, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_460, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_321, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_461, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_322, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_462, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_323, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_463, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))), inference(spm,[status(thm)],[c_0_317, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_464, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_324, c_0_113]), ['final']).
% 1.91/2.09  cnf(c_0_465, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_325, c_0_113]), ['final']).
% 1.91/2.09  cnf(c_0_466, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_326, c_0_113]), ['final']).
% 1.91/2.09  cnf(c_0_467, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_327, c_0_113]), ['final']).
% 1.91/2.09  cnf(c_0_468, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_328, c_0_329]), ['final']).
% 1.91/2.09  cnf(c_0_469, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_328, c_0_330]), ['final']).
% 1.91/2.09  cnf(c_0_470, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_471, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_472, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_240]), ['final']).
% 1.91/2.09  cnf(c_0_473, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_73, c_0_93]), ['final']).
% 1.91/2.09  cnf(c_0_474, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_331, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_475, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_331, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_476, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_332, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_477, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_332, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_478, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_333, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_479, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_333, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_480, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_334, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_481, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_334, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_482, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_335])).
% 1.91/2.09  cnf(c_0_483, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_335])).
% 1.91/2.09  cnf(c_0_484, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_335]), c_0_28])).
% 1.91/2.09  cnf(c_0_485, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_34, c_0_69])).
% 1.91/2.09  cnf(c_0_486, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_27, c_0_69])).
% 1.91/2.09  cnf(c_0_487, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_165])).
% 1.91/2.09  cnf(c_0_488, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_165])).
% 1.91/2.09  cnf(c_0_489, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_336, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_490, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_34, c_0_132])).
% 1.91/2.09  cnf(c_0_491, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_27, c_0_132])).
% 1.91/2.09  cnf(c_0_492, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_337, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_493, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_338]), c_0_28])).
% 1.91/2.09  cnf(c_0_494, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_339, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_495, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_340, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_496, plain, (k7_subset_1(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3),X4)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_341, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_497, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_498, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_39]), c_0_342])).
% 1.91/2.09  cnf(c_0_499, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_34, c_0_166])).
% 1.91/2.09  cnf(c_0_500, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_27, c_0_166])).
% 1.91/2.09  cnf(c_0_501, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_202, c_0_251])).
% 1.91/2.09  cnf(c_0_502, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X5))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_34, c_0_137])).
% 1.91/2.09  cnf(c_0_503, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_328, c_0_93]), ['final']).
% 1.91/2.09  cnf(c_0_504, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_343, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_505, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_201, c_0_213]), ['final']).
% 1.91/2.09  cnf(c_0_506, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)), inference(spm,[status(thm)],[c_0_154, c_0_214]), ['final']).
% 1.91/2.09  cnf(c_0_507, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_201, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_508, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))),k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_242, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_509, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_202, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_510, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))), inference(spm,[status(thm)],[c_0_155, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_511, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_203, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_512, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_154, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_513, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_34, c_0_344])).
% 1.91/2.09  cnf(c_0_514, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_27, c_0_344])).
% 1.91/2.09  cnf(c_0_515, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_34, c_0_345])).
% 1.91/2.09  cnf(c_0_516, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_27, c_0_345])).
% 1.91/2.09  cnf(c_0_517, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_167])).
% 1.91/2.09  cnf(c_0_518, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X4))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)), inference(spm,[status(thm)],[c_0_34, c_0_125])).
% 1.91/2.09  cnf(c_0_519, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X1|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_346, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_520, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_347, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_521, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_348, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_522, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)),X3)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_349, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_523, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_350, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_524, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_351, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_525, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_352, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_526, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_353, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_527, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_354, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_528, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_355, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_529, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_356, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_530, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_247, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_531, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_357, c_0_358]), c_0_28])).
% 1.91/2.09  cnf(c_0_532, plain, (r1_xboole_0(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_100, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_533, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_248, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_534, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_249, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_535, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359, c_0_58]), c_0_28])).
% 1.91/2.09  cnf(c_0_536, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_250, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_537, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_360, c_0_358]), c_0_28])).
% 1.91/2.09  cnf(c_0_538, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_361, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_539, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_362, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_540, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_363, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_541, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_364, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_542, plain, (k7_subset_1(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2),X3)=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X4)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_365, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_543, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_366, c_0_58]), c_0_28])).
% 1.91/2.09  cnf(c_0_544, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)),k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_367, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_545, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)),k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_367, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_546, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_356, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_547, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_356, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_548, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_368, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_549, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_369, c_0_41])).
% 1.91/2.09  cnf(c_0_550, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_370, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_551, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_371]), c_0_28])).
% 1.91/2.09  cnf(c_0_552, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_372]), c_0_28])).
% 1.91/2.09  cnf(c_0_553, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_373]), c_0_28])).
% 1.91/2.09  cnf(c_0_554, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_374]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_555, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_374]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_556, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_375]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_557, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_375]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_558, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_376]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_559, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_376]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_560, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_377]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_561, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_377]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_562, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_156])).
% 1.91/2.09  cnf(c_0_563, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_156])).
% 1.91/2.09  cnf(c_0_564, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_151])).
% 1.91/2.09  cnf(c_0_565, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_151])).
% 1.91/2.09  cnf(c_0_566, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_273])).
% 1.91/2.09  cnf(c_0_567, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_273])).
% 1.91/2.09  cnf(c_0_568, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_81])).
% 1.91/2.09  cnf(c_0_569, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_81])).
% 1.91/2.09  cnf(c_0_570, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_378, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_571, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_379, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_572, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_158])).
% 1.91/2.09  cnf(c_0_573, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_158])).
% 1.91/2.09  cnf(c_0_574, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_206, c_0_124])).
% 1.91/2.09  cnf(c_0_575, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_188, c_0_124])).
% 1.91/2.09  cnf(c_0_576, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_380])).
% 1.91/2.09  cnf(c_0_577, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_380])).
% 1.91/2.09  cnf(c_0_578, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_381])).
% 1.91/2.09  cnf(c_0_579, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_381])).
% 1.91/2.09  cnf(c_0_580, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_382])).
% 1.91/2.09  cnf(c_0_581, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_382])).
% 1.91/2.09  cnf(c_0_582, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_383])).
% 1.91/2.09  cnf(c_0_583, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_383])).
% 1.91/2.09  cnf(c_0_584, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))),k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_276, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_585, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_267, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_586, plain, (X1=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X1)))|~r1_xboole_0(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_374]), c_0_41])]), c_0_75]), ['final']).
% 1.91/2.09  cnf(c_0_587, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_46]), c_0_28])).
% 1.91/2.09  cnf(c_0_588, plain, (X1=X2|~r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X1)))|~r1_xboole_0(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_376]), c_0_41])]), c_0_75]), ['final']).
% 1.91/2.09  cnf(c_0_589, plain, (X1=X2|~r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X2)|~r1_xboole_0(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_377]), c_0_41])]), c_0_75]), ['final']).
% 1.91/2.09  cnf(c_0_590, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_266])).
% 1.91/2.09  cnf(c_0_591, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_186])).
% 1.91/2.09  cnf(c_0_592, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_384])).
% 1.91/2.09  cnf(c_0_593, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_384])).
% 1.91/2.09  cnf(c_0_594, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_177])).
% 1.91/2.09  cnf(c_0_595, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,X3))|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_176, c_0_371]), ['final']).
% 1.91/2.09  cnf(c_0_596, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,X3,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_168, c_0_372]), ['final']).
% 1.91/2.09  cnf(c_0_597, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X3)|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_176, c_0_373]), ['final']).
% 1.91/2.09  cnf(c_0_598, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X3)|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_168, c_0_49]), ['final']).
% 1.91/2.09  cnf(c_0_599, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X2)))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_134, c_0_385]), ['final']).
% 1.91/2.09  cnf(c_0_600, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,k1_xboole_0)))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_149, c_0_386]), ['final']).
% 1.91/2.09  cnf(c_0_601, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_387, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_602, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_388, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_603, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_389, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_604, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_201, c_0_201])).
% 1.91/2.09  cnf(c_0_605, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~r1_xboole_0(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_390, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_606, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_391, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_607, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_392, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_608, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_393, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_609, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_394, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_610, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_395, c_0_202])).
% 1.91/2.09  cnf(c_0_611, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_612, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_396, c_0_202])).
% 1.91/2.09  cnf(c_0_613, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_614, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_395, c_0_169])).
% 1.91/2.09  cnf(c_0_615, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_396, c_0_169])).
% 1.91/2.09  cnf(c_0_616, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X4)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_154, c_0_154])).
% 1.91/2.09  cnf(c_0_617, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_230, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_618, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X3)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_397, c_0_398])).
% 1.91/2.09  cnf(c_0_619, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_284, c_0_283]), ['final']).
% 1.91/2.09  cnf(c_0_620, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_399, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_621, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_399, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_622, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_400, c_0_399])).
% 1.91/2.09  cnf(c_0_623, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_134, c_0_401]), ['final']).
% 1.91/2.09  cnf(c_0_624, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X3)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_402, c_0_403])).
% 1.91/2.09  cnf(c_0_625, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X3,esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_404, c_0_405])).
% 1.91/2.09  cnf(c_0_626, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_118]), ['final']).
% 1.91/2.09  cnf(c_0_627, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_126, c_0_117]), ['final']).
% 1.91/2.09  cnf(c_0_628, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_406, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_629, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X3)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_397, c_0_397])).
% 1.91/2.09  cnf(c_0_630, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_407, c_0_397]), c_0_75])).
% 1.91/2.09  cnf(c_0_631, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X3)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_402, c_0_402])).
% 1.91/2.09  cnf(c_0_632, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X2,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_293, c_0_400]), c_0_75])).
% 1.91/2.09  cnf(c_0_633, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_224, c_0_290]), ['final']).
% 1.91/2.09  cnf(c_0_634, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_407, c_0_289]), c_0_75])).
% 1.91/2.09  cnf(c_0_635, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_408, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_636, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_409, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_637, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_294])).
% 1.91/2.09  cnf(c_0_638, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_410, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_639, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_411, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_640, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X3,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_404])).
% 1.91/2.09  cnf(c_0_641, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_412, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_642, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_413, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_643, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_297])).
% 1.91/2.09  cnf(c_0_644, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_414, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_645, negated_conjecture, (k7_subset_1(esk3_0,esk3_0,X1)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,X1)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_306, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_646, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_298]), c_0_80])])).
% 1.91/2.09  cnf(c_0_647, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k5_xboole_0(esk3_0,k1_xboole_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_415, c_0_228])).
% 1.91/2.09  cnf(c_0_648, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_163, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_649, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_120, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_650, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_416])).
% 1.91/2.09  cnf(c_0_651, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,X1)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_417])).
% 1.91/2.09  cnf(c_0_652, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_418, c_0_226]), ['final']).
% 1.91/2.09  cnf(c_0_653, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_419, c_0_228]), ['final']).
% 1.91/2.09  cnf(c_0_654, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_420, c_0_421])).
% 1.91/2.09  cnf(c_0_655, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_422, c_0_423])).
% 1.91/2.09  cnf(c_0_656, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_420, c_0_424])).
% 1.91/2.09  cnf(c_0_657, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_422, c_0_70])).
% 1.91/2.09  cnf(c_0_658, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_425, c_0_426]), ['final']).
% 1.91/2.09  cnf(c_0_659, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_420, c_0_299])).
% 1.91/2.09  cnf(c_0_660, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_427, c_0_428]), ['final']).
% 1.91/2.09  cnf(c_0_661, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_422, c_0_300])).
% 1.91/2.09  cnf(c_0_662, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_149, c_0_284]), ['final']).
% 1.91/2.09  cnf(c_0_663, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_149, c_0_224]), ['final']).
% 1.91/2.09  cnf(c_0_664, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_429, c_0_243])).
% 1.91/2.09  cnf(c_0_665, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_430, c_0_243])).
% 1.91/2.09  cnf(c_0_666, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_431, c_0_243])).
% 1.91/2.09  cnf(c_0_667, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_432, c_0_243])).
% 1.91/2.09  cnf(c_0_668, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_244, c_0_429])).
% 1.91/2.09  cnf(c_0_669, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_244, c_0_433])).
% 1.91/2.09  cnf(c_0_670, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_244, c_0_430])).
% 1.91/2.09  cnf(c_0_671, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_244, c_0_432])).
% 1.91/2.09  cnf(c_0_672, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_429])).
% 1.91/2.09  cnf(c_0_673, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_429])).
% 1.91/2.09  cnf(c_0_674, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_433])).
% 1.91/2.09  cnf(c_0_675, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_433])).
% 1.91/2.09  cnf(c_0_676, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_430])).
% 1.91/2.09  cnf(c_0_677, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_430])).
% 1.91/2.09  cnf(c_0_678, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_432])).
% 1.91/2.09  cnf(c_0_679, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_432])).
% 1.91/2.09  cnf(c_0_680, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_316, c_0_429])).
% 1.91/2.09  cnf(c_0_681, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_198, c_0_429])).
% 1.91/2.09  cnf(c_0_682, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_316, c_0_433])).
% 1.91/2.09  cnf(c_0_683, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_198, c_0_433])).
% 1.91/2.09  cnf(c_0_684, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_316, c_0_430])).
% 1.91/2.09  cnf(c_0_685, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_198, c_0_430])).
% 1.91/2.09  cnf(c_0_686, negated_conjecture, (esk3_0=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_302, c_0_303]), ['final']).
% 1.91/2.09  cnf(c_0_687, negated_conjecture, (esk3_0=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_301, c_0_434]), ['final']).
% 1.91/2.09  cnf(c_0_688, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_316, c_0_432])).
% 1.91/2.09  cnf(c_0_689, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_198, c_0_432])).
% 1.91/2.09  cnf(c_0_690, negated_conjecture, (esk3_0=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_302, c_0_301]), ['final']).
% 1.91/2.09  cnf(c_0_691, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_xboole_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_146, c_0_91])).
% 1.91/2.09  cnf(c_0_692, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,k1_xboole_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_91])).
% 1.91/2.09  cnf(c_0_693, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_435, c_0_35])).
% 1.91/2.09  cnf(c_0_694, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_436, c_0_35])).
% 1.91/2.09  cnf(c_0_695, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.09  cnf(c_0_696, plain, (k1_xboole_0=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X1),X1)), inference(spm,[status(thm)],[c_0_437, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_697, plain, (k1_xboole_0=X1|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X1,X2),X1)), inference(spm,[status(thm)],[c_0_304, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_698, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X1,k4_subset_1(X2,X3,X1))), inference(spm,[status(thm)],[c_0_438, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_699, plain, (X1=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X1,X2))), inference(spm,[status(thm)],[c_0_305, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_700, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_257, c_0_28])).
% 1.91/2.09  cnf(c_0_701, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_439, c_0_80])).
% 1.91/2.09  cnf(c_0_702, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_440, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_703, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_440, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_704, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_441, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_705, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_441, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_706, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_442, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_707, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_442, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_708, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X4,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_443, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_709, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X4),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_443, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_710, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_235]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_711, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_235]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_712, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_713, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_714, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_715, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_236]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_716, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_237]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_717, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_237]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_718, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_444, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_719, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_445, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_720, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_446, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_721, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)), inference(spm,[status(thm)],[c_0_447, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_722, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X2,X3,k1_xboole_0)),k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_448, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_723, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X2,X3,k1_xboole_0),X5),k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_448, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_724, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_449, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_725, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_450, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_726, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_451, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_727, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_452, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_728, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X2,k1_xboole_0,X3)),k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_453, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_729, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X2,k1_xboole_0,X3),X5),k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_453, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_730, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X4,X5,k4_subset_1(X2,X3,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_454, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_731, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X4,k4_subset_1(X2,X3,k1_xboole_0),X5))), inference(spm,[status(thm)],[c_0_454, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_732, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X4,X5,k4_subset_1(X2,k1_xboole_0,X3)))), inference(spm,[status(thm)],[c_0_455, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_733, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X4))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X4,k4_subset_1(X2,k1_xboole_0,X3),X5))), inference(spm,[status(thm)],[c_0_455, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_734, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)),k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_456, c_0_444]), ['final']).
% 1.91/2.09  cnf(c_0_735, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4),k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_457, c_0_444]), ['final']).
% 1.91/2.09  cnf(c_0_736, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_456, c_0_445]), ['final']).
% 1.91/2.09  cnf(c_0_737, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4))), inference(spm,[status(thm)],[c_0_457, c_0_445]), ['final']).
% 1.91/2.09  cnf(c_0_738, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)),k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_456, c_0_446]), ['final']).
% 1.91/2.09  cnf(c_0_739, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4),k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_457, c_0_446]), ['final']).
% 1.91/2.09  cnf(c_0_740, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_447]), ['final']).
% 1.91/2.09  cnf(c_0_741, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4))), inference(spm,[status(thm)],[c_0_457, c_0_447]), ['final']).
% 1.91/2.09  cnf(c_0_742, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X2,k1_xboole_0))),k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_458, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_743, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)),X4),k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_458, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_744, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_459, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_745, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_460, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_746, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(k1_xboole_0,X2))),k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_242]), ['final']).
% 1.91/2.09  cnf(c_0_747, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)),X4),k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_457, c_0_242]), ['final']).
% 1.91/2.09  cnf(c_0_748, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_461, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_749, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_462, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_750, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X2,k1_xboole_0))))), inference(spm,[status(thm)],[c_0_463, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_751, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k4_subset_1(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)),X4))), inference(spm,[status(thm)],[c_0_463, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_752, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_464, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_753, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_465, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_754, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(k1_xboole_0,X2))))), inference(spm,[status(thm)],[c_0_456, c_0_155]), ['final']).
% 1.91/2.09  cnf(c_0_755, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k3_tarski(k2_tarski(k1_xboole_0,X2)))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X3))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)),X4))), inference(spm,[status(thm)],[c_0_457, c_0_155]), ['final']).
% 1.91/2.09  cnf(c_0_756, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_466, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_757, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_467, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_758, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_338]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_759, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_338]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_760, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X2,k1_xboole_0,k1_xboole_0)),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_96]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_761, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X4),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_96]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_762, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_456, c_0_246]), ['final']).
% 1.91/2.09  cnf(c_0_763, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_457, c_0_246]), ['final']).
% 1.91/2.09  cnf(c_0_764, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_456, c_0_82]), ['final']).
% 1.91/2.09  cnf(c_0_765, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3))), inference(spm,[status(thm)],[c_0_457, c_0_82]), ['final']).
% 1.91/2.09  cnf(c_0_766, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_468, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_767, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_469, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_768, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_470, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_769, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_471, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_770, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k7_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_472, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_771, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X3)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_473, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_772, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_474, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_773, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_474, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_774, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_475, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_775, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_475, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_776, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_476, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_777, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_476, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_778, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_477, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_779, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_477, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_780, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_478, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_781, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_478, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_782, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_479, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_783, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_479, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_784, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_480, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_785, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_480, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_786, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_481, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_787, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_481, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_788, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_482, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_789, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_483, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_790, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_484, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_791, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_485, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_792, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_486, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_793, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))),k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_444, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_794, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)),k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_444, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_795, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))), inference(spm,[status(thm)],[c_0_445, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_796, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))), inference(spm,[status(thm)],[c_0_445, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_797, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))),k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_446, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_798, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)),k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_446, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_799, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))), inference(spm,[status(thm)],[c_0_447, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_800, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))), inference(spm,[status(thm)],[c_0_447, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_801, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_487, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_802, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_488, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_803, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_235, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_804, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_236, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_805, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_237, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_806, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_456, c_0_489]), ['final']).
% 1.91/2.09  cnf(c_0_807, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_490, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_808, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X2,X3,k1_xboole_0),X4)))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),X4)), inference(spm,[status(thm)],[c_0_491, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_809, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_457, c_0_489]), ['final']).
% 1.91/2.09  cnf(c_0_810, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_456, c_0_251]), ['final']).
% 1.91/2.09  cnf(c_0_811, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3))), inference(spm,[status(thm)],[c_0_457, c_0_251]), ['final']).
% 1.91/2.09  cnf(c_0_812, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_268]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_813, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_268]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_814, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_338]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_815, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_338]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_816, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_492]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_817, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_492]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_818, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_493, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_819, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_269]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_820, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_269]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_821, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_494]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_822, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_494]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_823, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_270]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_824, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_270]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_825, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_495]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_826, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_495]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_827, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_275]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_828, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_275]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_829, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,X5,k4_subset_1(X1,X2,X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_496]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_830, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X4,k4_subset_1(X1,X2,X3),X5))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_496]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_831, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k7_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_338, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_832, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_489]), ['final']).
% 1.91/2.09  cnf(c_0_833, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k7_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_73, c_0_121]), ['final']).
% 1.91/2.09  cnf(c_0_834, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_497]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_835, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_497]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_836, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_497]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_837, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_497]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_838, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_192]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_839, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_497, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_840, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_498, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_841, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_499, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_842, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(k4_subset_1(X2,k1_xboole_0,X3),X4)))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_500, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_843, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_121]), ['final']).
% 1.91/2.09  cnf(c_0_844, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_501, c_0_58]), ['final']).
% 1.91/2.09  cnf(c_0_845, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_489, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_846, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_489, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_847, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_251, c_0_28]), ['final']).
% 1.91/2.09  cnf(c_0_848, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))), inference(spm,[status(thm)],[c_0_251, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_849, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))), inference(spm,[status(thm)],[c_0_251, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_850, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),X4)), inference(spm,[status(thm)],[c_0_502, c_0_41]), ['final']).
% 1.91/2.09  cnf(c_0_851, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_328, c_0_121]), ['final']).
% 1.91/2.09  cnf(c_0_852, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_96]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_853, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)),k4_subset_1(X2,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_96]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_854, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)=k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X2)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_96, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_855, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k4_subset_1(X1,k1_xboole_0,k1_xboole_0)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_503]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_856, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X2))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X3),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_503]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_857, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_503]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_858, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_504, c_0_93]), ['final']).
% 1.91/2.09  cnf(c_0_859, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_503]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_860, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_503, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_861, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_246, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_862, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_246, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_863, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(X2,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))), inference(spm,[status(thm)],[c_0_82, c_0_38]), ['final']).
% 1.91/2.09  cnf(c_0_864, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k3_tarski(k2_tarski(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),X2)))), inference(spm,[status(thm)],[c_0_82, c_0_32]), ['final']).
% 1.91/2.09  cnf(c_0_865, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_456, c_0_505]), ['final']).
% 1.91/2.09  cnf(c_0_866, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_457, c_0_505]), ['final']).
% 1.91/2.09  cnf(c_0_867, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_456, c_0_272]), ['final']).
% 1.91/2.09  cnf(c_0_868, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_457, c_0_272]), ['final']).
% 1.91/2.09  cnf(c_0_869, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_456, c_0_506]), ['final']).
% 1.91/2.09  cnf(c_0_870, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_457, c_0_506]), ['final']).
% 1.91/2.09  cnf(c_0_871, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_219]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_872, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_219]), c_0_41])]), ['final']).
% 1.91/2.09  cnf(c_0_873, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_507]), ['final']).
% 1.91/2.09  cnf(c_0_874, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))),k4_subset_1(X2,X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_508, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_875, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_457, c_0_507]), ['final']).
% 1.91/2.09  cnf(c_0_876, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))),k4_subset_1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_508, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_877, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_247]), ['final']).
% 1.91/2.09  cnf(c_0_878, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_457, c_0_247]), ['final']).
% 1.91/2.09  cnf(c_0_879, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_509]), ['final']).
% 1.91/2.09  cnf(c_0_880, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k4_subset_1(X2,X3,k1_xboole_0))|~m1_subset_1(k4_subset_1(X2,X3,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k1_xboole_0),k3_tarski(k2_tarski(X4,k4_subset_1(X2,X3,k1_xboole_0))))), inference(spm,[status(thm)],[c_0_510, c_0_52]), ['final']).
% 1.91/2.09  cnf(c_0_881, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_457, c_0_509]), ['final']).
% 1.91/2.09  cnf(c_0_882, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,X3),k1_xboole_0)=k5_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k4_subset_1(X2,k1_xboole_0,X3))|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,X3),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X2,k1_xboole_0,X3))))), inference(spm,[status(thm)],[c_0_510, c_0_39]), ['final']).
% 1.91/2.09  cnf(c_0_883, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_456, c_0_248]), ['final']).
% 1.91/2.09  cnf(c_0_884, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_457, c_0_248]), ['final']).
% 1.91/2.09  cnf(c_0_885, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_456, c_0_511]), ['final']).
% 1.91/2.09  cnf(c_0_886, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_457, c_0_511]), ['final']).
% 1.91/2.09  cnf(c_0_887, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_456, c_0_249]), ['final']).
% 1.91/2.09  cnf(c_0_888, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_457, c_0_249]), ['final']).
% 1.91/2.09  cnf(c_0_889, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_456, c_0_512]), ['final']).
% 1.91/2.10  cnf(c_0_890, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_457, c_0_512]), ['final']).
% 1.91/2.10  cnf(c_0_891, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_456, c_0_250]), ['final']).
% 1.91/2.10  cnf(c_0_892, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_457, c_0_250]), ['final']).
% 1.91/2.10  cnf(c_0_893, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_513, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_894, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_514, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_895, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_515, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_896, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_516, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_897, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_517, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_898, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))),k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_508, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_899, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(k1_xboole_0,X2)))))|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X3)), inference(spm,[status(thm)],[c_0_518, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_900, plain, (k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_342, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_901, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_342, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_902, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X2,k1_xboole_0)))|~m1_subset_1(k3_tarski(k2_tarski(X2,k1_xboole_0)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k1_xboole_0)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,k1_xboole_0)))))), inference(spm,[status(thm)],[c_0_510, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_903, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_519]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_904, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_519]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_905, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_374]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_906, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_374]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_907, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_520]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_908, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_520]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_909, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_375]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_910, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_375]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_911, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_521]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_912, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_521]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_913, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_376]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_914, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_376]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_915, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_522]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_916, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_522]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_917, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,X4,k3_tarski(k2_tarski(X1,X2))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_377]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_918, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X2|~m1_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k4_subset_1(X3,k3_tarski(k2_tarski(X1,X2)),X4))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_377]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_919, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_523]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_920, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_523]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_921, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_524]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_922, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_524]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_923, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_525]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_924, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_525]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_925, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,X4,k4_subset_1(X1,X2,X2)))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_526]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_926, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X3,k4_subset_1(X1,X2,X2),X4))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_526]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_927, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_212, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_928, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_212]), ['final']).
% 1.91/2.10  cnf(c_0_929, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_201, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_930, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_201]), ['final']).
% 1.91/2.10  cnf(c_0_931, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_286, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_932, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_286, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_933, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_286]), ['final']).
% 1.91/2.10  cnf(c_0_934, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_286]), ['final']).
% 1.91/2.10  cnf(c_0_935, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_202, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_936, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_202]), ['final']).
% 1.91/2.10  cnf(c_0_937, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_203, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_938, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_504, c_0_203]), ['final']).
% 1.91/2.10  cnf(c_0_939, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_216, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_940, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_216, c_0_44]), ['final']).
% 1.91/2.10  cnf(c_0_941, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_154, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_942, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_154, c_0_44]), ['final']).
% 1.91/2.10  cnf(c_0_943, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_201, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_944, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_286, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_945, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_203, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_946, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_154, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_947, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_212, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_948, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_202, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_949, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_286, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_950, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_216, c_0_527]), ['final']).
% 1.91/2.10  cnf(c_0_951, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_201, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_952, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_286, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_953, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_203, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_954, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_154, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_955, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X4,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_212, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_956, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X3),X4)))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_202, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_957, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_286, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_958, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X4,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X4)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_216, c_0_328]), ['final']).
% 1.91/2.10  cnf(c_0_959, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k3_tarski(k2_tarski(k1_xboole_0,X1))),k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_456, c_0_528]), ['final']).
% 1.91/2.10  cnf(c_0_960, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)),X3),k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_457, c_0_528]), ['final']).
% 1.91/2.10  cnf(c_0_961, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k3_tarski(k2_tarski(X1,k1_xboole_0))),k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_456, c_0_276]), ['final']).
% 1.91/2.10  cnf(c_0_962, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)),X3),k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_457, c_0_276]), ['final']).
% 1.91/2.10  cnf(c_0_963, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k4_subset_1(X2,X3,k3_tarski(k2_tarski(k1_xboole_0,X1))))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_529, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_964, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k4_subset_1(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)),X3))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_529, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_965, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k4_subset_1(X2,X3,k3_tarski(k2_tarski(X1,k1_xboole_0))))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_456, c_0_267]), ['final']).
% 1.91/2.10  cnf(c_0_966, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)))=X1|~m1_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k4_subset_1(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)),X3))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_457, c_0_267]), ['final']).
% 1.91/2.10  cnf(c_0_967, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))), inference(spm,[status(thm)],[c_0_254, c_0_127]), ['final']).
% 1.91/2.10  cnf(c_0_968, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(X3,k4_subset_1(X2,X3,X3))), inference(spm,[status(thm)],[c_0_179, c_0_127]), ['final']).
% 1.91/2.10  cnf(c_0_969, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,k4_subset_1(X2,X3,X3))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_185, c_0_141]), ['final']).
% 1.91/2.10  cnf(c_0_970, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X4)=k5_xboole_0(k4_subset_1(X2,X3,X3),X3)|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X3),X4)|~r1_xboole_0(k4_subset_1(X2,X3,X3),X3)), inference(spm,[status(thm)],[c_0_256, c_0_141]), ['final']).
% 1.91/2.10  cnf(c_0_971, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_530, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_972, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_530, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_973, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_531, c_0_532]), ['final']).
% 1.91/2.10  cnf(c_0_974, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_533, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_975, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_533, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_976, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_534, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_977, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_534, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_978, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_535, c_0_113]), ['final']).
% 1.91/2.10  cnf(c_0_979, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_536, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_980, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_536, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_981, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_537, c_0_532]), ['final']).
% 1.91/2.10  cnf(c_0_982, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_538, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_983, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_539, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_984, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)|~r1_xboole_0(X4,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_540, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_985, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X1)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_541, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_986, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_505, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_987, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_505, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_988, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_202, c_0_213]), ['final']).
% 1.91/2.10  cnf(c_0_989, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_286, c_0_213]), ['final']).
% 1.91/2.10  cnf(c_0_990, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_286, c_0_214]), ['final']).
% 1.91/2.10  cnf(c_0_991, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_272, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_992, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_272, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_993, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X1,X1)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_542, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_994, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_506, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_995, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_506, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_996, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_543, c_0_113]), ['final']).
% 1.91/2.10  cnf(c_0_997, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)),k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_544, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_998, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4),k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_544, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_999, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)),k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_545, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1000, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4),k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_545, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1001, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,X4,k4_subset_1(X1,k1_xboole_0,X2)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_546, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1002, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X3,k4_subset_1(X1,k1_xboole_0,X2),X4))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_546, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1003, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,X4,k4_subset_1(X1,X2,k1_xboole_0)))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_547, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1004, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X3))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X3,k4_subset_1(X1,X2,k1_xboole_0),X4))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_547, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1005, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),X1)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_548, c_0_53]), c_0_100])]), ['final']).
% 1.91/2.10  cnf(c_0_1006, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_219]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1007, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=k5_xboole_0(k4_subset_1(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_219]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1008, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_549, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1009, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_507, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1010, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_507, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1011, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_509, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1012, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_509, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1013, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_511, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1014, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_511, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1015, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_212, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1016, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_212, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1017, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_286, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1018, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_286, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1019, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_286, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1020, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_286, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1021, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_512, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1022, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_512, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1023, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_216, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1024, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_216, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1025, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_201, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1026, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_286, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1027, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_203, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1028, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_154, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1029, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_212, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1030, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,X2),X3)))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_202, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1031, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_286, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1032, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X3)|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_216, c_0_550]), ['final']).
% 1.91/2.10  cnf(c_0_1033, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_551, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1034, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,X2,k1_xboole_0))))=k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_552, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1035, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k1_xboole_0,k4_subset_1(X1,k1_xboole_0,X2))))=k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)), inference(spm,[status(thm)],[c_0_553, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1036, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_554, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1037, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_554, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1038, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_555, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1039, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_555, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1040, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_556, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1041, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_556, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1042, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_557, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1043, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)),k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_557, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1044, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_558, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1045, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_558, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1046, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_559, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1047, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_559, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1048, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_560, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1049, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(X4,k4_subset_1(X1,X2,X3))))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_560, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1050, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_561, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1051, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k4_subset_1(X1,X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X3),X4)))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_561, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1052, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_562, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1053, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_563, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1054, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_564, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1055, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_565, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1056, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_566, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1057, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_567, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1058, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_568, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1059, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_569, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1060, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_570, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1061, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_571, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1062, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_572, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1063, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_573, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1064, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_574, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1065, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_575, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1066, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_576, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1067, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_577, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1068, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_578, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1069, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k1_setfam_1(k2_tarski(k4_subset_1(X1,k1_xboole_0,X2),X3)))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_579, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1070, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_580, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1071, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_581, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1072, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_582, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1073, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k1_setfam_1(k2_tarski(k4_subset_1(X1,X2,k1_xboole_0),X3)))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X3)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_583, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1074, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_523]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1075, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_523]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1076, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_524]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1077, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_524]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1078, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_525]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1079, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)),k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_525]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1080, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,X2))))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_526]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1081, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k4_subset_1(X1,X2,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),k3_tarski(k2_tarski(k4_subset_1(X1,X2,X2),X3)))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_526]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1082, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))),k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_584, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1083, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))),k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_584, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1084, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),k3_tarski(k2_tarski(X3,k4_subset_1(X1,k1_xboole_0,X2))))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_585, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1085, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0))=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),k3_tarski(k2_tarski(X3,k4_subset_1(X1,X2,k1_xboole_0))))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_585, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1086, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_519]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1087, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_519]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1088, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_520]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1089, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)),k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_520]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1090, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_521]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1091, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_521]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1092, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X2)))))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_522]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1093, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_522]), c_0_41])]), ['final']).
% 1.91/2.10  cnf(c_0_1094, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_519, c_0_189]), c_0_76])]), ['final']).
% 1.91/2.10  cnf(c_0_1095, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X1,X2))|~r1_xboole_0(X2,k4_subset_1(X3,X1,X2))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_586, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1096, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X2,X1))|~r1_xboole_0(X2,k4_subset_1(X3,X2,X1))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_586, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1097, plain, (X1=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_586, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1098, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_374, c_0_189]), c_0_80])]), ['final']).
% 1.91/2.10  cnf(c_0_1099, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_520, c_0_189]), c_0_76])]), ['final']).
% 1.91/2.10  cnf(c_0_1100, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_587, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1101, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_375, c_0_189]), c_0_80])]), ['final']).
% 1.91/2.10  cnf(c_0_1102, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_521, c_0_189]), c_0_76])]), ['final']).
% 1.91/2.10  cnf(c_0_1103, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X1,X2),X1)|~r1_xboole_0(X2,k4_subset_1(X3,X1,X2))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_588, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1104, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X2,X1),X1)|~r1_xboole_0(X2,k4_subset_1(X3,X2,X1))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_588, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1105, plain, (X1=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_588, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1106, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk3_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_376, c_0_189]), c_0_80])]), ['final']).
% 1.91/2.10  cnf(c_0_1107, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_522, c_0_189]), c_0_76])]), ['final']).
% 1.91/2.10  cnf(c_0_1108, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X1,X2),X1)|~r1_xboole_0(k4_subset_1(X3,X1,X2),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_589, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1109, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X2,X1),X1)|~r1_xboole_0(k4_subset_1(X3,X2,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_589, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1110, plain, (X1=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_589, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1111, negated_conjecture, (k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),X1)=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_377, c_0_189]), c_0_80])]), ['final']).
% 1.91/2.10  cnf(c_0_1112, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))),k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_528, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1113, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)),k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_528, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1114, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_590, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1115, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_591, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1116, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_592, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1117, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_593, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1118, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,k1_xboole_0)))))=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X2)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_594, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1119, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)))=X1|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(k1_xboole_0,X1)))))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_585, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1120, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))), inference(spm,[status(thm)],[c_0_117, c_0_127]), ['final']).
% 1.91/2.10  cnf(c_0_1121, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_47, c_0_141]), ['final']).
% 1.91/2.10  cnf(c_0_1122, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_595, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1123, plain, (k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_596, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1124, plain, (k7_subset_1(k4_subset_1(X1,k1_xboole_0,X2),k4_subset_1(X1,k1_xboole_0,X2),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_597, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1125, plain, (k7_subset_1(k4_subset_1(X1,X2,k1_xboole_0),k4_subset_1(X1,X2,k1_xboole_0),k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_598, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1126, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_599, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1127, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_600, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1128, plain, (k7_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),k3_tarski(k2_tarski(k1_xboole_0,X1)),k1_xboole_0)=k1_xboole_0|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_601, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1129, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)=k1_xboole_0|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_387, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1130, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_456, c_0_602]), ['final']).
% 1.91/2.10  cnf(c_0_1131, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_457, c_0_602]), ['final']).
% 1.91/2.10  cnf(c_0_1132, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_456, c_0_603]), ['final']).
% 1.91/2.10  cnf(c_0_1133, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_457, c_0_603]), ['final']).
% 1.91/2.10  cnf(c_0_1134, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_602, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1135, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_602, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1136, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_603, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1137, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_603, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1138, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,X1),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_456, c_0_201]), ['final']).
% 1.91/2.10  cnf(c_0_1139, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X1,X3),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_457, c_0_201]), ['final']).
% 1.91/2.10  cnf(c_0_1140, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|esk2_0!=k1_xboole_0|~r1_xboole_0(X2,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_604, c_0_426]), c_0_226]), c_0_227]), ['final']).
% 1.91/2.10  cnf(c_0_1141, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(X2,k2_struct_0(esk1_0))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_604, c_0_428]), c_0_228]), c_0_229]), ['final']).
% 1.91/2.10  cnf(c_0_1142, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_201, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1143, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_201, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1144, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,X1),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_456, c_0_605]), ['final']).
% 1.91/2.10  cnf(c_0_1145, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X1,X3),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_457, c_0_605]), ['final']).
% 1.91/2.10  cnf(c_0_1146, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_605, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1147, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_605, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1148, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_456, c_0_606]), ['final']).
% 1.91/2.10  cnf(c_0_1149, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_457, c_0_606]), ['final']).
% 1.91/2.10  cnf(c_0_1150, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_456, c_0_607]), ['final']).
% 1.91/2.10  cnf(c_0_1151, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_457, c_0_607]), ['final']).
% 1.91/2.10  cnf(c_0_1152, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_456, c_0_608]), ['final']).
% 1.91/2.10  cnf(c_0_1153, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_457, c_0_608]), ['final']).
% 1.91/2.10  cnf(c_0_1154, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_456, c_0_609]), ['final']).
% 1.91/2.10  cnf(c_0_1155, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k2_struct_0(esk1_0),X2),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_457, c_0_609]), ['final']).
% 1.91/2.10  cnf(c_0_1156, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_606, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1157, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_606, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1158, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_607, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1159, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_607, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1160, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_608, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1161, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_608, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1162, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_609, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1163, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)),k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_609, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1164, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X4,X1))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_456, c_0_202]), ['final']).
% 1.91/2.10  cnf(c_0_1165, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,k4_subset_1(X4,X1,X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_457, c_0_202]), ['final']).
% 1.91/2.10  cnf(c_0_1166, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_202, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1167, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_202, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1168, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|esk2_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_610, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1169, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_612, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1170, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,X1),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_456, c_0_203]), ['final']).
% 1.91/2.10  cnf(c_0_1171, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X1,X3),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_457, c_0_203]), ['final']).
% 1.91/2.10  cnf(c_0_1172, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_203, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1173, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_203, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1174, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X4,X1),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_456, c_0_169]), ['final']).
% 1.91/2.10  cnf(c_0_1175, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(k4_subset_1(X4,X1,X3),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_457, c_0_169]), ['final']).
% 1.91/2.10  cnf(c_0_1176, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X4,X1))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_456, c_0_169]), ['final']).
% 1.91/2.10  cnf(c_0_1177, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,k4_subset_1(X4,X1,X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_457, c_0_169]), ['final']).
% 1.91/2.10  cnf(c_0_1178, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X3,X1)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_169, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1179, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X3)),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_169, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1180, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_169, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1181, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_169, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1182, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|esk2_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_614, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1183, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_615, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1184, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_456, c_0_395]), ['final']).
% 1.91/2.10  cnf(c_0_1185, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_457, c_0_395]), ['final']).
% 1.91/2.10  cnf(c_0_1186, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,X2,k2_struct_0(esk1_0)))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_456, c_0_396]), ['final']).
% 1.91/2.10  cnf(c_0_1187, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X1,k2_struct_0(esk1_0),X2))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_457, c_0_396]), ['final']).
% 1.91/2.10  cnf(c_0_1188, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_395, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1189, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_395, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1190, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X1,k2_struct_0(esk1_0))))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_396, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1191, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X1)))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_396, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1192, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X4,X1))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_456, c_0_154]), ['final']).
% 1.91/2.10  cnf(c_0_1193, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,k4_subset_1(X4,X1,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_457, c_0_154]), ['final']).
% 1.91/2.10  cnf(c_0_1194, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|esk2_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_616, c_0_611]), c_0_226]), c_0_227]), ['final']).
% 1.91/2.10  cnf(c_0_1195, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),X2)|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_616, c_0_613]), c_0_228]), c_0_229]), ['final']).
% 1.91/2.10  cnf(c_0_1196, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_154, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1197, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_154, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1198, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X4,X1))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_456, c_0_617]), ['final']).
% 1.91/2.10  cnf(c_0_1199, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~r1_xboole_0(X1,k4_subset_1(X4,X1,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_457, c_0_617]), ['final']).
% 1.91/2.10  cnf(c_0_1200, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X3,X1)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_617, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1201, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k5_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X3)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_617, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1202, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_618, c_0_426]), c_0_28]), c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1203, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_149, c_0_619]), ['final']).
% 1.91/2.10  cnf(c_0_1204, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X1|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_134, c_0_619]), ['final']).
% 1.91/2.10  cnf(c_0_1205, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_224, c_0_283]), ['final']).
% 1.91/2.10  cnf(c_0_1206, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_61, c_0_283]), ['final']).
% 1.91/2.10  cnf(c_0_1207, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X3,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_283]), ['final']).
% 1.91/2.10  cnf(c_0_1208, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_620, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1209, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_621, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1210, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_622, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1211, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_623, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1212, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_624, c_0_428]), c_0_28]), c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1213, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_61, c_0_284]), ['final']).
% 1.91/2.10  cnf(c_0_1214, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_284]), ['final']).
% 1.91/2.10  cnf(c_0_1215, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_625, c_0_613]), c_0_28]), c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1216, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_168, c_0_626]), ['final']).
% 1.91/2.10  cnf(c_0_1217, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_168, c_0_127]), ['final']).
% 1.91/2.10  cnf(c_0_1218, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_176, c_0_127]), ['final']).
% 1.91/2.10  cnf(c_0_1219, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_176, c_0_627]), ['final']).
% 1.91/2.10  cnf(c_0_1220, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_628, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1221, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_628, c_0_39]), ['final']).
% 1.91/2.10  cnf(c_0_1222, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(esk2_0,X2)|~r1_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_629, c_0_426]), c_0_28]), c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1223, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_630, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1224, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X2|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_628, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1225, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_631, c_0_428]), c_0_28]), c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1226, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_632, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1227, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X2|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_149, c_0_633]), ['final']).
% 1.91/2.10  cnf(c_0_1228, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_134, c_0_633]), ['final']).
% 1.91/2.10  cnf(c_0_1229, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_400, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1230, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)|~m1_subset_1(k3_tarski(k2_tarski(k1_xboole_0,X2)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X2)),X2)), inference(spm,[status(thm)],[c_0_116, c_0_290]), ['final']).
% 1.91/2.10  cnf(c_0_1231, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X4,k3_tarski(k2_tarski(X2,X3)))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_61, c_0_290]), ['final']).
% 1.91/2.10  cnf(c_0_1232, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_35, c_0_290]), ['final']).
% 1.91/2.10  cnf(c_0_1233, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_634, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1234, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_635, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1235, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X4)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_35, c_0_224]), ['final']).
% 1.91/2.10  cnf(c_0_1236, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_168, c_0_141]), ['final']).
% 1.91/2.10  cnf(c_0_1237, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_176, c_0_141]), ['final']).
% 1.91/2.10  cnf(c_0_1238, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,X2),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_456, c_0_151]), ['final']).
% 1.91/2.10  cnf(c_0_1239, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X4,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X5,X2,X4),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_457, c_0_151]), ['final']).
% 1.91/2.10  cnf(c_0_1240, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,X2)),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_151, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1241, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X4)),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_151, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1242, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_456, c_0_636]), ['final']).
% 1.91/2.10  cnf(c_0_1243, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,esk2_0,X3),esk2_0)), inference(spm,[status(thm)],[c_0_457, c_0_636]), ['final']).
% 1.91/2.10  cnf(c_0_1244, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,k4_subset_1(X2,X3,esk2_0))), inference(spm,[status(thm)],[c_0_456, c_0_410]), ['final']).
% 1.91/2.10  cnf(c_0_1245, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,k4_subset_1(X2,esk2_0,X3))), inference(spm,[status(thm)],[c_0_457, c_0_410]), ['final']).
% 1.91/2.10  cnf(c_0_1246, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_637, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1247, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_636, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1248, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(esk2_0,X2)),esk2_0)), inference(spm,[status(thm)],[c_0_636, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1249, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_636, c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1250, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X2,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_410, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1251, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k3_tarski(k2_tarski(X2,esk2_0)))), inference(spm,[status(thm)],[c_0_410, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1252, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k3_tarski(k2_tarski(esk2_0,X2)))), inference(spm,[status(thm)],[c_0_410, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1253, negated_conjecture, (k7_subset_1(X1,esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_638, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1254, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(X3,k4_subset_1(X2,k1_xboole_0,k1_xboole_0))|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_639]), ['final']).
% 1.91/2.10  cnf(c_0_1255, plain, (k7_subset_1(X1,k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)=k1_xboole_0|~m1_subset_1(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k1_xboole_0,k1_xboole_0),X3)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_639]), ['final']).
% 1.91/2.10  cnf(c_0_1256, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~r1_xboole_0(X2,esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_611]), c_0_28]), c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1257, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_407, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1258, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(X2,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_640, c_0_428]), c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1259, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_641, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1260, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X4,X5,X2))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_456, c_0_81]), ['final']).
% 1.91/2.10  cnf(c_0_1261, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X4,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X5,X2,X4))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_457, c_0_81]), ['final']).
% 1.91/2.10  cnf(c_0_1262, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X4,X2)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1263, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X4)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1264, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_456, c_0_642]), ['final']).
% 1.91/2.10  cnf(c_0_1265, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,esk3_0,X3),esk3_0)), inference(spm,[status(thm)],[c_0_457, c_0_642]), ['final']).
% 1.91/2.10  cnf(c_0_1266, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_643, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1267, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_642, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1268, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(esk3_0,X2)),esk3_0)), inference(spm,[status(thm)],[c_0_642, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1269, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_642, c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1270, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,k4_subset_1(X2,X3,esk3_0))), inference(spm,[status(thm)],[c_0_456, c_0_120]), ['final']).
% 1.91/2.10  cnf(c_0_1271, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,k4_subset_1(X2,esk3_0,X3))), inference(spm,[status(thm)],[c_0_457, c_0_120]), ['final']).
% 1.91/2.10  cnf(c_0_1272, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X2,esk3_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_120, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1273, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k4_subset_1(X1,X2,esk3_0))), inference(spm,[status(thm)],[c_0_456, c_0_644]), ['final']).
% 1.91/2.10  cnf(c_0_1274, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k4_subset_1(X1,esk3_0,X2))), inference(spm,[status(thm)],[c_0_457, c_0_644]), ['final']).
% 1.91/2.10  cnf(c_0_1275, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_35, c_0_234]), ['final']).
% 1.91/2.10  cnf(c_0_1276, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,k3_tarski(k2_tarski(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_644, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1277, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,k3_tarski(k2_tarski(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_644, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1278, negated_conjecture, (k7_subset_1(esk3_0,esk3_0,k2_struct_0(esk1_0))=k7_subset_1(esk3_0,esk3_0,esk2_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_645, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1279, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,k2_struct_0(esk1_0))=k7_subset_1(esk3_0,esk3_0,esk2_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_439, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1280, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_163]), ['final']).
% 1.91/2.10  cnf(c_0_1281, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_646, c_0_41]), ['final']).
% 1.91/2.10  cnf(c_0_1282, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_456, c_0_163]), ['final']).
% 1.91/2.10  cnf(c_0_1283, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,esk3_0,X2),esk3_0)), inference(spm,[status(thm)],[c_0_457, c_0_163]), ['final']).
% 1.91/2.10  cnf(c_0_1284, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_163, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1285, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(k3_tarski(k2_tarski(X1,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_163, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1286, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(k3_tarski(k2_tarski(esk3_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_163, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1287, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_647, c_0_234]), ['final']).
% 1.91/2.10  cnf(c_0_1288, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_648, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1289, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k3_tarski(k2_tarski(X2,esk3_0)))), inference(spm,[status(thm)],[c_0_120, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1290, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k3_tarski(k2_tarski(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_120, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1291, negated_conjecture, (k7_subset_1(X1,esk3_0,esk2_0)=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_649, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1292, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X4,X5,X2),X2)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_456, c_0_135]), ['final']).
% 1.91/2.10  cnf(c_0_1293, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X4,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X5,X2,X4),X2)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_457, c_0_135]), ['final']).
% 1.91/2.10  cnf(c_0_1294, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_416, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1295, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(esk3_0,X2)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_650, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1296, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_417, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1297, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~r1_xboole_0(esk3_0,X1)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_651, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1298, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X4,X2)),X2)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_135, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1299, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,X4)),X2)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_135, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1300, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X4,X5,X2))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_456, c_0_124]), ['final']).
% 1.91/2.10  cnf(c_0_1301, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X4,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X5,X2,X4))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_457, c_0_124]), ['final']).
% 1.91/2.10  cnf(c_0_1302, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X4,X2)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_124, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1303, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k3_tarski(k2_tarski(X2,X4)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_124, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1304, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_94, c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1305, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_231, c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1306, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_652, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1307, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,k1_xboole_0,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_168, c_0_118]), ['final']).
% 1.91/2.10  cnf(c_0_1308, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(X2,esk3_0)), inference(spm,[status(thm)],[c_0_653, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1309, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,k1_xboole_0))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_176, c_0_117]), ['final']).
% 1.91/2.10  cnf(c_0_1310, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_654, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1311, plain, (k5_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,k1_xboole_0,X2),X2)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_168, c_0_126]), ['final']).
% 1.91/2.10  cnf(c_0_1312, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_655, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1313, plain, (k5_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)=X2|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,k1_xboole_0),X2)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_176, c_0_47]), ['final']).
% 1.91/2.10  cnf(c_0_1314, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_656, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1315, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|~r1_xboole_0(esk2_0,X2)), inference(spm,[status(thm)],[c_0_424, c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1316, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_657, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1317, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_70, c_0_228]), ['final']).
% 1.91/2.10  cnf(c_0_1318, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(X1,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_658]), ['final']).
% 1.91/2.10  cnf(c_0_1319, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k5_xboole_0(esk2_0,esk2_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_659, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1320, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(X1,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_660]), ['final']).
% 1.91/2.10  cnf(c_0_1321, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k5_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_661, c_0_428]), ['final']).
% 1.91/2.10  cnf(c_0_1322, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_176, c_0_118]), ['final']).
% 1.91/2.10  cnf(c_0_1323, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_168, c_0_117]), ['final']).
% 1.91/2.10  cnf(c_0_1324, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_176, c_0_126]), ['final']).
% 1.91/2.10  cnf(c_0_1325, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_xboole_0)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_168, c_0_47]), ['final']).
% 1.91/2.10  cnf(c_0_1326, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)=X1|~r1_xboole_0(X1,k3_tarski(k2_tarski(k1_xboole_0,X1)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_149, c_0_283]), ['final']).
% 1.91/2.10  cnf(c_0_1327, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)=X1|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,k1_xboole_0)))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_134, c_0_284]), ['final']).
% 1.91/2.10  cnf(c_0_1328, plain, (k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)=X1|~r1_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X1)),X1)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_149, c_0_290]), ['final']).
% 1.91/2.10  cnf(c_0_1329, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_134, c_0_224]), ['final']).
% 1.91/2.10  cnf(c_0_1330, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)=X1|~r1_xboole_0(X2,k3_tarski(k2_tarski(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_662, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1331, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,k4_subset_1(X1,X2,X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_176, c_0_117]), ['final']).
% 1.91/2.10  cnf(c_0_1332, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0)=X1|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_663, c_0_28]), ['final']).
% 1.91/2.10  cnf(c_0_1333, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X2),X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_176, c_0_47]), ['final']).
% 1.91/2.10  cnf(c_0_1334, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_664, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1335, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_665, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1336, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_666, c_0_426]), ['final']).
% 1.91/2.10  cnf(c_0_1337, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,X3,k2_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_667, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1338, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_668, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1339, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))), inference(spm,[status(thm)],[c_0_669, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1340, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,k2_struct_0(esk1_0),X3),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_670, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1341, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),k4_subset_1(X2,k2_struct_0(esk1_0),X3))), inference(spm,[status(thm)],[c_0_671, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1342, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_672, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1343, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_673, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1344, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_674, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1345, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_675, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1346, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_676, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1347, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(X1,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_677, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1348, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,k2_struct_0(esk1_0))))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_678, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1349, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),X1)))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X2))|~r1_xboole_0(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_679, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1350, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(k4_subset_1(X2,X3,X1),X1)), inference(spm,[status(thm)],[c_0_162, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_1351, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(k4_subset_1(X3,X1,X2),X1)), inference(spm,[status(thm)],[c_0_162, c_0_44]), ['final']).
% 1.91/2.10  cnf(c_0_1352, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X1,k4_subset_1(X2,X3,X1))), inference(spm,[status(thm)],[c_0_87, c_0_42]), ['final']).
% 1.91/2.10  cnf(c_0_1353, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_680, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1354, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_681, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1355, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X1,k4_subset_1(X3,X1,X2))), inference(spm,[status(thm)],[c_0_87, c_0_44]), ['final']).
% 1.91/2.10  cnf(c_0_1356, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_682, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1357, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))), inference(spm,[status(thm)],[c_0_683, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1358, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_684, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1359, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)),k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_685, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1360, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|~r1_xboole_0(X2,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_303]), ['final']).
% 1.91/2.10  cnf(c_0_1361, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(X2,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_434]), ['final']).
% 1.91/2.10  cnf(c_0_1362, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),X2)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(k2_struct_0(esk1_0),X2)), inference(spm,[status(thm)],[c_0_35, c_0_434]), ['final']).
% 1.91/2.10  cnf(c_0_1363, negated_conjecture, (esk3_0=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_686, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1364, negated_conjecture, (esk3_0=esk2_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_434, c_0_303]), ['final']).
% 1.91/2.10  cnf(c_0_1365, negated_conjecture, (esk3_0=esk2_0|esk2_0!=k1_xboole_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_687, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1366, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(X2,k2_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_688, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1367, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k2_struct_0(esk1_0))=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_xboole_0(k2_struct_0(esk1_0),k3_tarski(k2_tarski(k2_struct_0(esk1_0),X2)))), inference(spm,[status(thm)],[c_0_689, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1368, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_162, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1369, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_162, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1370, negated_conjecture, (esk3_0=esk2_0|esk3_0!=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_690, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1371, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_87, c_0_38]), ['final']).
% 1.91/2.10  cnf(c_0_1372, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_87, c_0_32]), ['final']).
% 1.91/2.10  cnf(c_0_1373, negated_conjecture, (k5_xboole_0(esk2_0,esk2_0)=k5_xboole_0(esk2_0,k1_xboole_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_691, c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1374, negated_conjecture, (k5_xboole_0(esk2_0,esk2_0)=k5_xboole_0(esk2_0,k1_xboole_0)|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_692, c_0_226]), ['final']).
% 1.91/2.10  cnf(c_0_1375, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|esk3_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_693, c_0_613]), ['final']).
% 1.91/2.10  cnf(c_0_1376, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_xboole_0)=esk3_0|esk2_0!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_694, c_0_611]), ['final']).
% 1.91/2.10  cnf(c_0_1377, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_695, c_0_253]), ['final']).
% 1.91/2.10  cnf(c_0_1378, negated_conjecture, (k4_subset_1(X1,esk3_0,esk2_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_189, c_0_52]), ['final']).
% 1.91/2.10  cnf(c_0_1379, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_696, c_0_128]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.10  cnf(c_0_1380, negated_conjecture, (esk2_0=k1_xboole_0|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_697, c_0_128]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.10  cnf(c_0_1381, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(esk3_0,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_698, c_0_128]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.10  cnf(c_0_1382, negated_conjecture, (esk2_0=k1_xboole_0|~r1_xboole_0(esk2_0,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_699, c_0_128]), c_0_68]), c_0_91])]), ['final']).
% 1.91/2.10  cnf(c_0_1383, negated_conjecture, (~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_695, c_0_436]), ['final']).
% 1.91/2.10  cnf(c_0_1384, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,k1_xboole_0)),k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)=k5_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_700, c_0_56]), ['final']).
% 1.91/2.10  cnf(c_0_1385, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0)=k7_subset_1(esk3_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_701, c_0_76]), ['final']).
% 1.91/2.10  cnf(c_0_1386, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0)))=k7_subset_1(esk3_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_95, c_0_234]), ['final']).
% 1.91/2.10  cnf(c_0_1387, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 1.91/2.10  # SZS output end Saturation
% 1.91/2.10  # Proof object total steps             : 1388
% 1.91/2.10  # Proof object clause steps            : 1363
% 1.91/2.10  # Proof object formula steps           : 25
% 1.91/2.10  # Proof object conjectures             : 356
% 1.91/2.10  # Proof object clause conjectures      : 353
% 1.91/2.10  # Proof object formula conjectures     : 3
% 1.91/2.10  # Proof object initial clauses used    : 18
% 1.91/2.10  # Proof object initial formulas used   : 12
% 1.91/2.10  # Proof object generating inferences   : 1332
% 1.91/2.10  # Proof object simplifying inferences  : 379
% 1.91/2.10  # Parsed axioms                        : 12
% 1.91/2.10  # Removed by relevancy pruning/SinE    : 0
% 1.91/2.10  # Initial clauses                      : 18
% 1.91/2.10  # Removed in clause preprocessing      : 4
% 1.91/2.10  # Initial clauses in saturation        : 14
% 1.91/2.10  # Processed clauses                    : 46931
% 1.91/2.10  # ...of these trivial                  : 59
% 1.91/2.10  # ...subsumed                          : 44761
% 1.91/2.10  # ...remaining for further processing  : 2111
% 1.91/2.10  # Other redundant clauses eliminated   : 8
% 1.91/2.10  # Clauses deleted for lack of memory   : 0
% 1.91/2.10  # Backward-subsumed                    : 987
% 1.91/2.10  # Backward-rewritten                   : 21
% 1.91/2.10  # Generated clauses                    : 51798
% 1.91/2.10  # ...of the previous two non-trivial   : 51543
% 1.91/2.10  # Contextual simplify-reflections      : 10
% 1.91/2.10  # Paramodulations                      : 51790
% 1.91/2.10  # Factorizations                       : 0
% 1.91/2.10  # Equation resolutions                 : 8
% 1.91/2.10  # Propositional unsat checks           : 0
% 1.91/2.10  #    Propositional check models        : 0
% 1.91/2.10  #    Propositional check unsatisfiable : 0
% 1.91/2.10  #    Propositional clauses             : 0
% 1.91/2.10  #    Propositional clauses after purity: 0
% 1.91/2.10  #    Propositional unsat core size     : 0
% 1.91/2.10  #    Propositional preprocessing time  : 0.000
% 1.91/2.10  #    Propositional encoding time       : 0.000
% 1.91/2.10  #    Propositional solver time         : 0.000
% 1.91/2.10  #    Success case prop preproc time    : 0.000
% 1.91/2.10  #    Success case prop encoding time   : 0.000
% 1.91/2.10  #    Success case prop solver time     : 0.000
% 1.91/2.10  # Current number of processed clauses  : 1089
% 1.91/2.10  #    Positive orientable unit clauses  : 24
% 1.91/2.10  #    Positive unorientable unit clauses: 1
% 1.91/2.10  #    Negative unit clauses             : 2
% 1.91/2.10  #    Non-unit-clauses                  : 1062
% 1.91/2.10  # Current number of unprocessed clauses: 0
% 1.91/2.10  # ...number of literals in the above   : 0
% 1.91/2.10  # Current number of archived formulas  : 0
% 1.91/2.10  # Current number of archived clauses   : 1026
% 1.91/2.10  # Clause-clause subsumption calls (NU) : 2762971
% 1.91/2.10  # Rec. Clause-clause subsumption calls : 201645
% 1.91/2.10  # Non-unit clause-clause subsumptions  : 45742
% 1.91/2.10  # Unit Clause-clause subsumption calls : 5
% 1.91/2.10  # Rewrite failures with RHS unbound    : 0
% 1.91/2.10  # BW rewrite match attempts            : 52
% 1.91/2.10  # BW rewrite match successes           : 14
% 1.91/2.10  # Condensation attempts                : 0
% 1.91/2.10  # Condensation successes               : 0
% 1.91/2.10  # Termbank termtop insertions          : 1483250
% 1.91/2.10  
% 1.91/2.10  # -------------------------------------------------
% 1.91/2.10  # User time                : 1.754 s
% 1.91/2.10  # System time              : 0.007 s
% 1.91/2.10  # Total time               : 1.761 s
% 1.91/2.10  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
