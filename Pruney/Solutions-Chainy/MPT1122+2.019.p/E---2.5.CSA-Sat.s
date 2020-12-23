%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:16 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 414 expanded)
%              Number of clauses        :   47 ( 189 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :    7
%              Number of atoms          :  178 (1007 expanded)
%              Number of equality atoms :   44 ( 273 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_12,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_13,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k7_subset_1(X8,X9,X10) = k4_xboole_0(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
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

cnf(c_0_23,plain,
    ( k7_subset_1(X1,k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_24,plain,
    ( k7_subset_1(X1,X1,X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21]),
    [final]).

fof(c_0_25,negated_conjecture,
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

fof(c_0_26,plain,(
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
    ( m1_subset_1(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),k1_zfmisc_1(k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23]),
    [final]).

cnf(c_0_31,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_24]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
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
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_38,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k1_zfmisc_1(k7_subset_1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(k4_xboole_0(X1,X2),k7_subset_1(X1,k4_xboole_0(X1,X2),X3),X4) = k4_xboole_0(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_23]),
    [final]).

cnf(c_0_42,plain,
    ( k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3) = k4_xboole_0(k7_subset_1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31]),
    [final]).

cnf(c_0_43,plain,
    ( r1_tarski(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_32])).

cnf(c_0_45,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)) != k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31]),
    [final]).

cnf(c_0_46,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [final]).

cnf(c_0_47,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31]),
    [final]).

cnf(c_0_48,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2)) != k4_xboole_0(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20]),
    [final]).

cnf(c_0_49,plain,
    ( k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2)) = k4_xboole_0(u1_struct_0(X1),X2)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20]),
    [final]).

cnf(c_0_50,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_36]),
    [final]).

cnf(c_0_51,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | k2_pre_topc(X1,u1_struct_0(X1)) != u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_52,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,esk2_0) != esk2_0
    | ~ v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_39])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_39])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_60,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4) = k4_xboole_0(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_40]),
    [final]).

cnf(c_0_61,plain,
    ( k7_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5) = k4_xboole_0(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_62,plain,
    ( m1_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k1_zfmisc_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3) = k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_42]),
    [final]).

cnf(c_0_65,plain,
    ( r1_tarski(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_24]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_24]),
    [final]).

cnf(c_0_67,plain,
    ( r1_tarski(k7_subset_1(X1,X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.014 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # No proof found!
% 0.13/0.36  # SZS status CounterSatisfiable
% 0.13/0.36  # SZS output start Saturation
% 0.13/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.36  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.36  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.36  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.36  fof(t53_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.13/0.36  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.36  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.13/0.36  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.36  fof(c_0_10, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.36  fof(c_0_11, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.36  fof(c_0_12, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.36  fof(c_0_13, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.36  fof(c_0_14, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|k7_subset_1(X8,X9,X10)=k4_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.36  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.36  cnf(c_0_17, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_18, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.36  cnf(c_0_20, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.13/0.36  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.13/0.36  fof(c_0_22, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t53_pre_topc])).
% 0.13/0.36  cnf(c_0_23, plain, (k7_subset_1(X1,k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.13/0.36  cnf(c_0_24, plain, (k7_subset_1(X1,X1,X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_21]), ['final']).
% 0.13/0.36  fof(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((((v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)))&(~v3_pre_topc(esk2_0,esk1_0)|v3_pre_topc(esk2_0,esk1_0)))&(((v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))&(~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])).
% 0.13/0.36  fof(c_0_26, plain, ![X18, X19]:((~v4_pre_topc(X19,X18)|k2_pre_topc(X18,X19)=X19|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~v2_pre_topc(X18)|k2_pre_topc(X18,X19)!=X19|v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.36  fof(c_0_27, plain, ![X13, X14]:((~v4_pre_topc(X14,X13)|v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)|v4_pre_topc(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.13/0.36  fof(c_0_28, plain, ![X16, X17]:(~l1_struct_0(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),k7_subset_1(u1_struct_0(X16),k2_struct_0(X16),X17))=X17)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.36  fof(c_0_29, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.36  cnf(c_0_30, plain, (m1_subset_1(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),k1_zfmisc_1(k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_20, c_0_23]), ['final']).
% 0.13/0.36  cnf(c_0_31, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_24]), ['final']).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_33, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.13/0.36  cnf(c_0_34, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.13/0.36  cnf(c_0_35, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.13/0.36  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.13/0.36  cnf(c_0_37, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.13/0.36  cnf(c_0_38, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_40, plain, (m1_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k1_zfmisc_1(k7_subset_1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_24]), ['final']).
% 0.13/0.36  cnf(c_0_41, plain, (k7_subset_1(k4_xboole_0(X1,X2),k7_subset_1(X1,k4_xboole_0(X1,X2),X3),X4)=k4_xboole_0(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_23, c_0_23]), ['final']).
% 0.13/0.36  cnf(c_0_42, plain, (k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)=k4_xboole_0(k7_subset_1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_19, c_0_31]), ['final']).
% 0.13/0.36  cnf(c_0_43, plain, (r1_tarski(k7_subset_1(X1,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_23]), ['final']).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_32])).
% 0.13/0.36  cnf(c_0_45, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2))!=k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_31]), ['final']).
% 0.13/0.36  cnf(c_0_46, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['final']).
% 0.13/0.36  cnf(c_0_47, plain, (k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_31]), ['final']).
% 0.13/0.36  cnf(c_0_48, plain, (v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2))!=k4_xboole_0(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_20]), ['final']).
% 0.13/0.36  cnf(c_0_49, plain, (k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2))=k4_xboole_0(u1_struct_0(X1),X2)|~v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_20]), ['final']).
% 0.13/0.36  cnf(c_0_50, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_36]), ['final']).
% 0.13/0.36  cnf(c_0_51, plain, (v4_pre_topc(u1_struct_0(X1),X1)|k2_pre_topc(X1,u1_struct_0(X1))!=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.13/0.36  cnf(c_0_52, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_21]), ['final']).
% 0.13/0.36  cnf(c_0_53, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,esk2_0)!=esk2_0|~v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_32]), c_0_39])]), ['final']).
% 0.13/0.36  cnf(c_0_54, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_39])]), ['final']).
% 0.13/0.36  cnf(c_0_55, negated_conjecture, (k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_57, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_60, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4)=k4_xboole_0(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_19, c_0_40]), ['final']).
% 0.13/0.36  cnf(c_0_61, plain, (k7_subset_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5)=k4_xboole_0(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),X5)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.13/0.36  cnf(c_0_62, plain, (m1_subset_1(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k1_zfmisc_1(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)))), inference(spm,[status(thm)],[c_0_30, c_0_42]), ['final']).
% 0.13/0.36  cnf(c_0_63, plain, (r1_tarski(k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),X4),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3))), inference(spm,[status(thm)],[c_0_43, c_0_42]), ['final']).
% 0.13/0.36  cnf(c_0_64, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3)=k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_24, c_0_42]), ['final']).
% 0.13/0.36  cnf(c_0_65, plain, (r1_tarski(k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3),k7_subset_1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_24]), ['final']).
% 0.13/0.36  cnf(c_0_66, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_44, c_0_24]), ['final']).
% 0.13/0.36  cnf(c_0_67, plain, (r1_tarski(k7_subset_1(X1,X1,X2),X1)), inference(spm,[status(thm)],[c_0_16, c_0_24]), ['final']).
% 0.13/0.36  # SZS output end Saturation
% 0.13/0.36  # Proof object total steps             : 68
% 0.13/0.36  # Proof object clause steps            : 47
% 0.13/0.36  # Proof object formula steps           : 21
% 0.13/0.36  # Proof object conjectures             : 13
% 0.13/0.36  # Proof object clause conjectures      : 10
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 18
% 0.13/0.36  # Proof object initial formulas used   : 10
% 0.13/0.36  # Proof object generating inferences   : 27
% 0.13/0.36  # Proof object simplifying inferences  : 8
% 0.13/0.36  # Parsed axioms                        : 10
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 20
% 0.13/0.36  # Removed in clause preprocessing      : 3
% 0.13/0.36  # Initial clauses in saturation        : 17
% 0.13/0.36  # Processed clauses                    : 119
% 0.13/0.36  # ...of these trivial                  : 33
% 0.13/0.36  # ...subsumed                          : 21
% 0.13/0.36  # ...remaining for further processing  : 65
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 4
% 0.13/0.36  # Generated clauses                    : 130
% 0.13/0.36  # ...of the previous two non-trivial   : 87
% 0.13/0.36  # Contextual simplify-reflections      : 2
% 0.13/0.36  # Paramodulations                      : 130
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 44
% 0.13/0.36  #    Positive orientable unit clauses  : 17
% 0.13/0.36  #    Positive unorientable unit clauses: 4
% 0.13/0.36  #    Negative unit clauses             : 0
% 0.13/0.36  #    Non-unit-clauses                  : 23
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 22
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 227
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 73
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.36  # Unit Clause-clause subsumption calls : 44
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 15
% 0.13/0.36  # BW rewrite match successes           : 7
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 3144
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.020 s
% 0.13/0.36  # System time              : 0.002 s
% 0.13/0.36  # Total time               : 0.022 s
% 0.13/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
