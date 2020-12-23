%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1989+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 169 expanded)
%              Number of clauses        :   28 (  52 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  284 (1188 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v4_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(d6_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v4_waybel_7(X2,X1)
          <=> ? [X3] :
                ( ~ v1_xboole_0(X3)
                & v1_waybel_0(X3,X1)
                & v12_waybel_0(X3,X1)
                & v1_waybel_7(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                & X2 = k1_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(t37_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v1_waybel_7(k5_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(t34_waybel_0,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v5_waybel_6(X2,X1)
             => v4_waybel_7(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_waybel_7])).

fof(c_0_10,plain,(
    ! [X5,X6,X8] :
      ( ( ~ v1_xboole_0(esk1_2(X5,X6))
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v1_waybel_0(esk1_2(X5,X6),X5)
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v12_waybel_0(esk1_2(X5,X6),X5)
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v1_waybel_7(esk1_2(X5,X6),X5)
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( X6 = k1_yellow_0(X5,esk1_2(X5,X6))
        | ~ v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v1_xboole_0(X8)
        | ~ v1_waybel_0(X8,X5)
        | ~ v12_waybel_0(X8,X5)
        | ~ v1_waybel_7(X8,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | X6 != k1_yellow_0(X5,X8)
        | v4_waybel_7(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ l1_orders_2(X9)
      | m1_subset_1(k1_yellow_0(X9,X10),u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | m1_subset_1(k5_waybel_0(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

fof(c_0_13,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & v2_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & v5_waybel_6(esk3_0,esk2_0)
    & ~ v4_waybel_7(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ v1_lattice3(X19)
      | ~ v2_lattice3(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ v5_waybel_6(X20,X19)
      | v1_waybel_7(k5_waybel_0(X19,X20),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X15,X16))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) )
      & ( v1_waybel_0(k5_waybel_0(X15,X16),X15)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v4_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | v12_waybel_0(k5_waybel_0(X13,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(X3,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != k1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v5_waybel_6(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ( r1_yellow_0(X17,k5_waybel_0(X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( k1_yellow_0(X17,k5_waybel_0(X17,X18)) = X18
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(k1_yellow_0(X2,X1),X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_34,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk2_0,esk3_0),esk2_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_27]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk2_0,esk3_0),esk2_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_26]),c_0_21])])).

cnf(c_0_37,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(k5_waybel_0(esk2_0,esk3_0))
    | v4_waybel_7(k1_yellow_0(esk2_0,k5_waybel_0(esk2_0,esk3_0)),esk2_0)
    | v2_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_21])]),c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k1_yellow_0(esk2_0,k5_waybel_0(esk2_0,esk3_0)) = esk3_0
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_25]),c_0_26]),c_0_27]),c_0_21])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v4_waybel_7(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_41,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v2_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k5_waybel_0(esk2_0,esk3_0))
    | v2_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_20]),c_0_27]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
