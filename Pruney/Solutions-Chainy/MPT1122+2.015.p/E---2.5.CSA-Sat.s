%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:15 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  126 (2265 expanded)
%              Number of clauses        :  101 (1083 expanded)
%              Number of leaves         :   12 ( 574 expanded)
%              Depth                    :   11
%              Number of atoms          :  273 (4475 expanded)
%              Number of equality atoms :  114 (1671 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   11 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t53_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
             => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k3_subset_1(X7,X8) = k4_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k7_subset_1(X12,X13,X14) = k4_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18]),
    [final]).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21]),
    [final]).

fof(c_0_28,plain,(
    ! [X9] : m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_29,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
              & ( ( v2_pre_topc(X1)
                  & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
               => v3_pre_topc(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_pre_topc])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k3_subset_1(X1,X2),k1_setfam_1(k2_tarski(k3_subset_1(X1,X2),X3))) = k7_subset_1(X1,k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21]),
    [final]).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( v2_pre_topc(esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( v2_pre_topc(esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ( ~ v4_pre_topc(X23,X22)
        | k2_pre_topc(X22,X23) = X23
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ v2_pre_topc(X22)
        | k2_pre_topc(X22,X23) != X23
        | v4_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),X3))) = k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_41,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_42,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

fof(c_0_43,plain,(
    ! [X17,X18] :
      ( ( ~ v4_pre_topc(X18,X17)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18),X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18),X17)
        | v4_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_44,plain,(
    ! [X20,X21] :
      ( ~ l1_struct_0(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k7_subset_1(u1_struct_0(X20),k2_struct_0(X20),k7_subset_1(u1_struct_0(X20),k2_struct_0(X20),X21)) = X21 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_45,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_47,plain,
    ( k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3))) = k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1))) = k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40]),
    [final]).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39]),
    [final]).

cnf(c_0_52,plain,
    ( k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X1)),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,X1)),X2))) = k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_39]),
    [final]).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_39]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1))) = k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40]),
    [final]).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))) = k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39]),
    [final]).

cnf(c_0_56,plain,
    ( k5_xboole_0(k3_subset_1(X1,X1),k1_setfam_1(k2_tarski(k3_subset_1(X1,X1),X2))) = k7_subset_1(X1,k3_subset_1(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39]),
    [final]).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1)))) = k3_subset_1(X1,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39]),
    [final]).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_39]),
    [final]).

cnf(c_0_59,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) != k3_subset_1(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_60,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),X2)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_61,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_62,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_64,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,esk2_0) != esk2_0
    | ~ v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_46])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_67,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)))))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_47]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1))))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1)))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48]),
    [final]).

cnf(c_0_70,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_47]),
    [final]).

cnf(c_0_71,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),X2))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),X2)))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,k3_subset_1(X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48]),
    [final]).

cnf(c_0_72,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1))))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48]),
    [final]).

cnf(c_0_74,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_47]),
    [final]).

cnf(c_0_75,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),X2))))))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),X2)))))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_48]),
    [final]).

cnf(c_0_76,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47]),
    [final]).

cnf(c_0_78,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))) != k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_21]),
    [final]).

cnf(c_0_79,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_21]),
    [final]).

cnf(c_0_80,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [final]).

cnf(c_0_81,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))) != k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39]),
    [final]).

cnf(c_0_82,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_62]),c_0_63]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_40]),c_0_46])]),
    [final]).

cnf(c_0_84,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))) = k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_46])]),
    [final]).

cnf(c_0_86,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | k2_pre_topc(X1,u1_struct_0(X1)) != u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39]),
    [final]).

cnf(c_0_87,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | v4_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,esk2_0) != esk2_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_46])]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_93,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49]),
    [final]).

cnf(c_0_95,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50]),
    [final]).

cnf(c_0_98,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52]),
    [final]).

cnf(c_0_99,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51]),
    [final]).

cnf(c_0_103,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51]),
    [final]).

cnf(c_0_104,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52]),
    [final]).

cnf(c_0_105,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_53]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53]),
    [final]).

cnf(c_0_107,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_52]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40]),
    [final]).

cnf(c_0_110,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_50]),
    [final]).

cnf(c_0_115,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))) = k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_52]),
    [final]).

cnf(c_0_116,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54]),
    [final]).

cnf(c_0_120,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) = k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_40]),
    [final]).

cnf(c_0_123,plain,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.13/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(t53_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.13/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.38  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.13/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(c_0_12, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|k3_subset_1(X7,X8)=k4_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.38  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  fof(c_0_19, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_21, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.13/0.38  fof(c_0_22, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k7_subset_1(X12,X13,X14)=k4_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.38  cnf(c_0_23, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_25, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_21]), ['final']).
% 0.13/0.38  fof(c_0_28, plain, ![X9]:m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_29, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  fof(c_0_30, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t53_pre_topc])).
% 0.13/0.38  cnf(c_0_31, plain, (k5_xboole_0(k3_subset_1(X1,X2),k1_setfam_1(k2_tarski(k3_subset_1(X1,X2),X3)))=k7_subset_1(X1,k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_33, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_35, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((((v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)))&(~v3_pre_topc(esk2_0,esk1_0)|v3_pre_topc(esk2_0,esk1_0)))&(((v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))&(~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X22, X23]:((~v4_pre_topc(X23,X22)|k2_pre_topc(X22,X23)=X23|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(~v2_pre_topc(X22)|k2_pre_topc(X22,X23)!=X23|v4_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_37, plain, (k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),X3)))=k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_38, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_42, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.38  fof(c_0_43, plain, ![X17, X18]:((~v4_pre_topc(X18,X17)|v3_pre_topc(k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18),X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18),X17)|v4_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.13/0.38  fof(c_0_44, plain, ![X20, X21]:(~l1_struct_0(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|k7_subset_1(u1_struct_0(X20),k2_struct_0(X20),k7_subset_1(u1_struct_0(X20),k2_struct_0(X20),X21))=X21)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.38  fof(c_0_45, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_47, plain, (k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)))=k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))))), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1)))=k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1)), inference(spm,[status(thm)],[c_0_37, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))), inference(spm,[status(thm)],[c_0_32, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_52, plain, (k5_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X1)),k1_setfam_1(k2_tarski(k3_subset_1(X1,k3_subset_1(X1,X1)),X2)))=k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_53, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1))))), inference(spm,[status(thm)],[c_0_27, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)))=k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))))=k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_56, plain, (k5_xboole_0(k3_subset_1(X1,X1),k1_setfam_1(k2_tarski(k3_subset_1(X1,X1),X2)))=k7_subset_1(X1,k3_subset_1(X1,X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1))))=k3_subset_1(X1,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_23, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_20, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_59, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))!=k3_subset_1(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_60, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),X2)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_61, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.13/0.38  cnf(c_0_62, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.13/0.38  cnf(c_0_64, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,esk2_0)!=esk2_0|~v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_46])]), ['final']).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_67, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),X3)))))))|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_68, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1)))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),X1)))))))|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))), inference(spm,[status(thm)],[c_0_50, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_70, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_71, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),X2)))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),X2)))))))|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,k3_subset_1(X1,X1))))), inference(spm,[status(thm)],[c_0_52, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_72, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1)))))))|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_54, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_74, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_75, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),X2)))))))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),X2)))))))|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_76, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_77, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))),k3_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_78, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)))!=k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_59, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_79, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)))=k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_60, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_80, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['final']).
% 0.13/0.38  cnf(c_0_81, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))!=k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_82, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_62]), c_0_63]), ['final']).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_40]), c_0_46])]), ['final']).
% 0.13/0.38  cnf(c_0_84, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))=k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_60, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_46])]), ['final']).
% 0.13/0.38  cnf(c_0_86, plain, (v4_pre_topc(u1_struct_0(X1),X1)|k2_pre_topc(X1,u1_struct_0(X1))!=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_87, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|v4_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,esk2_0)!=esk2_0), inference(spm,[status(thm)],[c_0_65, c_0_66]), ['final']).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_46])]), ['final']).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_92, negated_conjecture, (v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_93, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))))), inference(spm,[status(thm)],[c_0_52, c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))))), inference(spm,[status(thm)],[c_0_50, c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_95, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))))), inference(spm,[status(thm)],[c_0_52, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_96, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))), inference(spm,[status(thm)],[c_0_53, c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_98, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))))), inference(spm,[status(thm)],[c_0_53, c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_99, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))))), inference(spm,[status(thm)],[c_0_56, c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_100, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))), inference(spm,[status(thm)],[c_0_54, c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_101, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))), inference(spm,[status(thm)],[c_0_55, c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_102, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))), inference(spm,[status(thm)],[c_0_54, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_103, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))))), inference(spm,[status(thm)],[c_0_56, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_104, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))))), inference(spm,[status(thm)],[c_0_55, c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_105, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))))), inference(spm,[status(thm)],[c_0_56, c_0_53]), ['final']).
% 0.13/0.38  cnf(c_0_106, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))), inference(spm,[status(thm)],[c_0_54, c_0_53]), ['final']).
% 0.13/0.38  cnf(c_0_107, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1))))), inference(spm,[status(thm)],[c_0_57, c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_108, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))), inference(spm,[status(thm)],[c_0_57, c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_109, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))), inference(spm,[status(thm)],[c_0_38, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_110, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))))), inference(spm,[status(thm)],[c_0_56, c_0_55]), ['final']).
% 0.13/0.38  cnf(c_0_111, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.13/0.38  cnf(c_0_112, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))), inference(spm,[status(thm)],[c_0_32, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_113, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))), inference(spm,[status(thm)],[c_0_27, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_114, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_58, c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_115, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))=k3_subset_1(k3_subset_1(X1,k3_subset_1(X1,X1)),k3_subset_1(X1,k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_58, c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_116, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_56]), ['final']).
% 0.13/0.38  cnf(c_0_117, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_54]), ['final']).
% 0.13/0.38  cnf(c_0_118, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_25, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_119, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_54]), ['final']).
% 0.13/0.38  cnf(c_0_120, plain, (k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))=k3_subset_1(k3_subset_1(X1,X1),k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_58, c_0_56]), ['final']).
% 0.13/0.38  cnf(c_0_121, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_122, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_123, plain, (k7_subset_1(X1,X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_124, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_125, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_63, c_0_46]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 126
% 0.13/0.38  # Proof object clause steps            : 101
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 38
% 0.13/0.38  # Proof object clause conjectures      : 35
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 78
% 0.13/0.38  # Proof object simplifying inferences  : 14
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 16
% 0.13/0.38  # Processed clauses                    : 113
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 110
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 88
% 0.13/0.38  # ...of the previous two non-trivial   : 81
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 88
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 94
% 0.13/0.38  #    Positive orientable unit clauses  : 46
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 48
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 19
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 441
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 191
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 195
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 304
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8057
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.041 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
