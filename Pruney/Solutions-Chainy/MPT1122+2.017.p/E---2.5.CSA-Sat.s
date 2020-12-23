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
% DateTime   : Thu Dec  3 11:09:16 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 339 expanded)
%              Number of clauses        :   42 ( 154 expanded)
%              Number of leaves         :   10 (  88 expanded)
%              Depth                    :    7
%              Number of atoms          :  168 ( 829 expanded)
%              Number of equality atoms :   48 ( 303 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

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

fof(c_0_10,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k7_subset_1(X10,X11,X12) = k4_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_11,plain,(
    ! [X8,X9] : k6_subset_1(X8,X9) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_12,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_13,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_14,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X6,X7] : m1_subset_1(k6_subset_1(X6,X7),k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_17,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k6_subset_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18]),
    [final]).

fof(c_0_22,negated_conjecture,(
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

fof(c_0_23,plain,(
    ! [X18,X19] :
      ( ( ~ v4_pre_topc(X19,X18)
        | k2_pre_topc(X18,X19) = X19
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ v2_pre_topc(X18)
        | k2_pre_topc(X18,X19) != X19
        | v4_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_24,plain,
    ( k7_subset_1(X1,k6_subset_1(X1,X2),X3) = k6_subset_1(k6_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_25,plain,
    ( k7_subset_1(X1,X1,X2) = k6_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21]),
    [final]).

fof(c_0_26,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( ~ v4_pre_topc(X14,X13)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)
        | v4_pre_topc(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ~ l1_struct_0(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),X17)) = X17 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_29,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_31,plain,
    ( m1_subset_1(k7_subset_1(X1,k6_subset_1(X1,X2),X3),k1_zfmisc_1(k6_subset_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_24]),
    [final]).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_34,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_35,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_37,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_38,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_39,plain,
    ( k2_pre_topc(X1,k6_subset_1(u1_struct_0(X1),X2)) = k6_subset_1(u1_struct_0(X1),X2)
    | ~ v4_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_41,plain,
    ( m1_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k1_zfmisc_1(k7_subset_1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25]),
    [final]).

cnf(c_0_42,plain,
    ( k7_subset_1(k6_subset_1(X1,X2),k7_subset_1(X1,k6_subset_1(X1,X2),X3),X4) = k6_subset_1(k7_subset_1(X1,k6_subset_1(X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_24,c_0_24]),
    [final]).

cnf(c_0_43,plain,
    ( k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3) = k6_subset_1(k7_subset_1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_32]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k6_subset_1(esk2_0,X1) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_33])).

cnf(c_0_45,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [final]).

cnf(c_0_46,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_36]),
    [final]).

cnf(c_0_47,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)) != k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32]),
    [final]).

cnf(c_0_48,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25]),
    [final]).

cnf(c_0_49,plain,
    ( v4_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k6_subset_1(u1_struct_0(X1),X2)) != k6_subset_1(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20]),
    [final]).

cnf(c_0_50,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | k2_pre_topc(X1,u1_struct_0(X1)) != u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_51,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,esk2_0) != esk2_0
    | ~ v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_40])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_40])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_58,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4) = k6_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_41]),
    [final]).

cnf(c_0_59,plain,
    ( k7_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5) = k6_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_60,plain,
    ( m1_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k1_zfmisc_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43]),
    [final]).

cnf(c_0_61,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3) = k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_25]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.37  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.20/0.37  fof(t53_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.20/0.37  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.37  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.20/0.37  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.20/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.37  fof(c_0_10, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|k7_subset_1(X10,X11,X12)=k4_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.37  fof(c_0_11, plain, ![X8, X9]:k6_subset_1(X8,X9)=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.37  fof(c_0_12, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.37  fof(c_0_13, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.37  cnf(c_0_14, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_16, plain, ![X6, X7]:m1_subset_1(k6_subset_1(X6,X7),k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.20/0.37  cnf(c_0_17, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_18, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k6_subset_1(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.20/0.37  cnf(c_0_20, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.20/0.37  fof(c_0_22, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t53_pre_topc])).
% 0.20/0.37  fof(c_0_23, plain, ![X18, X19]:((~v4_pre_topc(X19,X18)|k2_pre_topc(X18,X19)=X19|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~v2_pre_topc(X18)|k2_pre_topc(X18,X19)!=X19|v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.37  cnf(c_0_24, plain, (k7_subset_1(X1,k6_subset_1(X1,X2),X3)=k6_subset_1(k6_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_25, plain, (k7_subset_1(X1,X1,X2)=k6_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_21]), ['final']).
% 0.20/0.37  fof(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((((v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)))&(~v3_pre_topc(esk2_0,esk1_0)|v3_pre_topc(esk2_0,esk1_0)))&(((v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))&(~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])).
% 0.20/0.37  fof(c_0_27, plain, ![X13, X14]:((~v4_pre_topc(X14,X13)|v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)|v4_pre_topc(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.20/0.37  fof(c_0_28, plain, ![X16, X17]:(~l1_struct_0(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),X17))=X17)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.20/0.37  fof(c_0_29, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.37  cnf(c_0_30, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.20/0.37  cnf(c_0_31, plain, (m1_subset_1(k7_subset_1(X1,k6_subset_1(X1,X2),X3),k1_zfmisc_1(k6_subset_1(X1,X2)))), inference(spm,[status(thm)],[c_0_20, c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_32, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_25]), ['final']).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_34, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_35, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.20/0.37  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_37, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_38, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.20/0.37  cnf(c_0_39, plain, (k2_pre_topc(X1,k6_subset_1(u1_struct_0(X1),X2))=k6_subset_1(u1_struct_0(X1),X2)|~v4_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_41, plain, (m1_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k1_zfmisc_1(k7_subset_1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_25]), ['final']).
% 0.20/0.37  cnf(c_0_42, plain, (k7_subset_1(k6_subset_1(X1,X2),k7_subset_1(X1,k6_subset_1(X1,X2),X3),X4)=k6_subset_1(k7_subset_1(X1,k6_subset_1(X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_24, c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_43, plain, (k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)=k6_subset_1(k7_subset_1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_19, c_0_32]), ['final']).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (k6_subset_1(esk2_0,X1)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_33])).
% 0.20/0.37  cnf(c_0_45, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['final']).
% 0.20/0.37  cnf(c_0_46, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_35]), c_0_36]), ['final']).
% 0.20/0.37  cnf(c_0_47, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2))!=k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_32]), ['final']).
% 0.20/0.37  cnf(c_0_48, plain, (k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_25]), ['final']).
% 0.20/0.37  cnf(c_0_49, plain, (v4_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k6_subset_1(u1_struct_0(X1),X2))!=k6_subset_1(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_50, plain, (v4_pre_topc(u1_struct_0(X1),X1)|k2_pre_topc(X1,u1_struct_0(X1))!=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.20/0.37  cnf(c_0_51, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,esk2_0)!=esk2_0|~v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_40])]), ['final']).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, (k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_40])]), ['final']).
% 0.20/0.37  cnf(c_0_55, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_57, negated_conjecture, (v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_58, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4)=k6_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_19, c_0_41]), ['final']).
% 0.20/0.37  cnf(c_0_59, plain, (k7_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5)=k6_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5)), inference(spm,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.20/0.37  cnf(c_0_60, plain, (m1_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k1_zfmisc_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)))), inference(spm,[status(thm)],[c_0_31, c_0_43]), ['final']).
% 0.20/0.37  cnf(c_0_61, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3)=k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_25, c_0_43]), ['final']).
% 0.20/0.37  cnf(c_0_62, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_44, c_0_25]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 63
% 0.20/0.37  # Proof object clause steps            : 42
% 0.20/0.37  # Proof object formula steps           : 21
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 17
% 0.20/0.37  # Proof object initial formulas used   : 10
% 0.20/0.37  # Proof object generating inferences   : 22
% 0.20/0.37  # Proof object simplifying inferences  : 9
% 0.20/0.37  # Parsed axioms                        : 10
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 19
% 0.20/0.37  # Removed in clause preprocessing      : 4
% 0.20/0.37  # Initial clauses in saturation        : 15
% 0.20/0.37  # Processed clauses                    : 107
% 0.20/0.37  # ...of these trivial                  : 25
% 0.20/0.37  # ...subsumed                          : 21
% 0.20/0.37  # ...remaining for further processing  : 61
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 9
% 0.20/0.37  # Generated clauses                    : 112
% 0.20/0.37  # ...of the previous two non-trivial   : 85
% 0.20/0.37  # Contextual simplify-reflections      : 2
% 0.20/0.37  # Paramodulations                      : 112
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 37
% 0.20/0.37  #    Positive orientable unit clauses  : 12
% 0.20/0.37  #    Positive unorientable unit clauses: 4
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 21
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 26
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 157
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 46
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.20/0.37  # Unit Clause-clause subsumption calls : 24
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 30
% 0.20/0.37  # BW rewrite match successes           : 15
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3190
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.036 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
