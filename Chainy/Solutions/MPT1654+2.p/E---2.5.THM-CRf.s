%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1654+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 14.62s
% Output     : CNFRefutation 14.62s
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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT017+2.ax',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT017+2.ax',dt_k6_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT025+2.ax',t38_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT025+2.ax',t39_yellow_0)).

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
    ! [X6188] :
      ( ~ l1_orders_2(X6188)
      | l1_struct_0(X6188) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1198_0)
    & v3_orders_2(esk1198_0)
    & v4_orders_2(esk1198_0)
    & v5_orders_2(esk1198_0)
    & l1_orders_2(esk1198_0)
    & m1_subset_1(esk1199_0,u1_struct_0(esk1198_0))
    & ( ~ r1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0))
      | k1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0)) != esk1199_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_13,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X6183,X6184] :
      ( v1_xboole_0(X6183)
      | ~ m1_subset_1(X6184,X6183)
      | m1_subset_1(k6_domain_1(X6183,X6184),k1_zfmisc_1(X6183)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_struct_0(esk1198_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X10006,X10007] :
      ( v2_struct_0(X10006)
      | ~ l1_orders_2(X10006)
      | ~ m1_subset_1(X10007,u1_struct_0(X10006))
      | k5_waybel_0(X10006,X10007) = k3_waybel_0(X10006,k6_domain_1(u1_struct_0(X10006),X10007)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_waybel_0])])])])).

fof(c_0_20,plain,(
    ! [X9680,X9681] :
      ( ( r1_yellow_0(X9680,k6_domain_1(u1_struct_0(X9680),X9681))
        | ~ m1_subset_1(X9681,u1_struct_0(X9680))
        | v2_struct_0(X9680)
        | ~ v3_orders_2(X9680)
        | ~ v5_orders_2(X9680)
        | ~ l1_orders_2(X9680) )
      & ( r2_yellow_0(X9680,k6_domain_1(u1_struct_0(X9680),X9681))
        | ~ m1_subset_1(X9681,u1_struct_0(X9680))
        | v2_struct_0(X9680)
        | ~ v3_orders_2(X9680)
        | ~ v5_orders_2(X9680)
        | ~ l1_orders_2(X9680) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_0])])])])])).

fof(c_0_21,plain,(
    ! [X10243,X10244] :
      ( ( ~ r1_yellow_0(X10243,X10244)
        | r1_yellow_0(X10243,k3_waybel_0(X10243,X10244))
        | ~ m1_subset_1(X10244,k1_zfmisc_1(u1_struct_0(X10243)))
        | v2_struct_0(X10243)
        | ~ v3_orders_2(X10243)
        | ~ v4_orders_2(X10243)
        | ~ l1_orders_2(X10243) )
      & ( ~ r1_yellow_0(X10243,k3_waybel_0(X10243,X10244))
        | r1_yellow_0(X10243,X10244)
        | ~ m1_subset_1(X10244,k1_zfmisc_1(u1_struct_0(X10243)))
        | v2_struct_0(X10243)
        | ~ v3_orders_2(X10243)
        | ~ v4_orders_2(X10243)
        | ~ l1_orders_2(X10243) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_0])])])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk1199_0,u1_struct_0(esk1198_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1198_0)) ),
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
    ( v5_orders_2(esk1198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk1198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X9682,X9683] :
      ( ( k1_yellow_0(X9682,k6_domain_1(u1_struct_0(X9682),X9683)) = X9683
        | ~ m1_subset_1(X9683,u1_struct_0(X9682))
        | v2_struct_0(X9682)
        | ~ v3_orders_2(X9682)
        | ~ v5_orders_2(X9682)
        | ~ l1_orders_2(X9682) )
      & ( k2_yellow_0(X9682,k6_domain_1(u1_struct_0(X9682),X9683)) = X9683
        | ~ m1_subset_1(X9683,u1_struct_0(X9682))
        | v2_struct_0(X9682)
        | ~ v3_orders_2(X9682)
        | ~ v5_orders_2(X9682)
        | ~ l1_orders_2(X9682) ) ) ),
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
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1198_0),esk1199_0),k1_zfmisc_1(u1_struct_0(esk1198_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k3_waybel_0(esk1198_0,k6_domain_1(u1_struct_0(esk1198_0),esk1199_0)) = k5_waybel_0(esk1198_0,esk1199_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_14])]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_yellow_0(esk1198_0,k6_domain_1(u1_struct_0(esk1198_0),esk1199_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27]),c_0_28]),c_0_14])]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk1198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_35,plain,(
    ! [X10245,X10246] :
      ( v2_struct_0(X10245)
      | ~ v3_orders_2(X10245)
      | ~ v4_orders_2(X10245)
      | ~ l1_orders_2(X10245)
      | ~ m1_subset_1(X10246,k1_zfmisc_1(u1_struct_0(X10245)))
      | ~ r1_yellow_0(X10245,X10246)
      | k1_yellow_0(X10245,X10246) = k1_yellow_0(X10245,k3_waybel_0(X10245,X10246)) ) ),
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
    ( ~ r1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0))
    | k1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0)) != esk1199_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( r1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0)) ),
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
    ( k1_yellow_0(esk1198_0,k6_domain_1(u1_struct_0(esk1198_0),esk1199_0)) = esk1199_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_27]),c_0_28]),c_0_14])]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1198_0,k5_waybel_0(esk1198_0,esk1199_0)) != esk1199_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_32]),c_0_40]),c_0_33]),c_0_34]),c_0_28]),c_0_14])]),c_0_41]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
