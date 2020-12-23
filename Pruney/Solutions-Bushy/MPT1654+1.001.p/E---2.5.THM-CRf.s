%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1654+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:32 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 197 expanded)
%              Number of clauses        :   24 (  63 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 (1111 expanded)
%              Number of equality atoms :   18 ( 127 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
            & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_waybel_0)).

fof(t38_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
            & r2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_0)).

fof(t32_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_yellow_0(X1,X2)
          <=> r1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_0)).

fof(t39_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

fof(t33_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_yellow_0(X1,X2)
           => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
              & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_waybel_0])).

fof(c_0_10,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ r1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0))
      | k1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_13,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( v1_xboole_0(X5)
      | ~ m1_subset_1(X6,X5)
      | m1_subset_1(k6_domain_1(X5,X6),k1_zfmisc_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X3,X4] :
      ( v2_struct_0(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | k5_waybel_0(X3,X4) = k3_waybel_0(X3,k6_domain_1(u1_struct_0(X3),X4)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_waybel_0])])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( r1_yellow_0(X15,k6_domain_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_yellow_0(X15,k6_domain_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_0])])])])])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ( ~ r1_yellow_0(X11,X12)
        | r1_yellow_0(X11,k3_waybel_0(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_yellow_0(X11,k3_waybel_0(X11,X12))
        | r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_0])])])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ( k1_yellow_0(X17,k6_domain_1(u1_struct_0(X17),X18)) = X18
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( k2_yellow_0(X17,k6_domain_1(u1_struct_0(X17),X18)) = X18
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_0])])])])])).

cnf(c_0_30,plain,
    ( r1_yellow_0(X1,k3_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k3_waybel_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) = k5_waybel_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_14])]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27]),c_0_28]),c_0_14])]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v3_orders_2(X13)
      | ~ v4_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ r1_yellow_0(X13,X14)
      | k1_yellow_0(X13,X14) = k1_yellow_0(X13,k3_waybel_0(X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_0])])])])).

cnf(c_0_36,plain,
    ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0))
    | k1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( r1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_28]),c_0_14])]),c_0_18])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k1_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_27]),c_0_28]),c_0_14])]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_32]),c_0_40]),c_0_33]),c_0_34]),c_0_28]),c_0_14])]),c_0_41]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
