%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (1375 expanded)
%              Number of clauses        :   45 ( 442 expanded)
%              Number of leaves         :   10 ( 342 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (9107 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   70 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_waybel_7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d1_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(k12_lattice3(X1,X3,X4),X2)
                        & ~ r2_hidden(X3,X2)
                        & ~ r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_7)).

fof(t17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k5_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(d6_waybel_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r1_orders_2(X1,k11_lattice3(X1,X3,X4),X2)
                        & ~ r1_orders_2(X1,X3,X2)
                        & ~ r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_6)).

fof(c_0_10,negated_conjecture,(
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
             => v1_waybel_7(k5_waybel_0(X1,X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_waybel_7])).

fof(c_0_11,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_12,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_lattice3(esk5_0)
    & v2_lattice3(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & v5_waybel_6(esk6_0,esk5_0)
    & ~ v1_waybel_7(k5_waybel_0(esk5_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | m1_subset_1(k5_waybel_0(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v4_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | v12_waybel_0(k5_waybel_0(X20,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X22,X23))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22)) )
      & ( v1_waybel_0(k5_waybel_0(X22,X23),X22)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v1_waybel_7(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(k12_lattice3(X6,X8,X9),X7)
        | r2_hidden(X8,X7)
        | r2_hidden(X9,X7)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v1_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),u1_struct_0(X6))
        | v1_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(k12_lattice3(X6,esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | v1_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk1_2(X6,X7),X7)
        | v1_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),X7)
        | v1_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v2_lattice3(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_waybel_7])])])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r2_hidden(X29,k5_waybel_0(X27,X28))
        | r1_orders_2(X27,X29,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X29,X28)
        | r2_hidden(X29,k5_waybel_0(X27,X28))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])]),c_0_22])).

fof(c_0_32,plain,(
    ! [X24,X25,X26] :
      ( ~ v5_orders_2(X24)
      | ~ v2_lattice3(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | k12_lattice3(X24,X25,X26) = k11_lattice3(X24,X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25]),c_0_16])]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_27]),c_0_16])]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_waybel_7(k5_waybel_0(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(k5_waybel_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_27]),c_0_16])]),c_0_22])).

fof(c_0_39,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r1_orders_2(X12,k11_lattice3(X12,X14,X15),X13)
        | r1_orders_2(X12,X14,X13)
        | r1_orders_2(X12,X15,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk3_2(X12,X13),u1_struct_0(X12))
        | v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk4_2(X12,X13),u1_struct_0(X12))
        | v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r1_orders_2(X12,k11_lattice3(X12,esk3_2(X12,X13),esk4_2(X12,X13)),X13)
        | v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk3_2(X12,X13),X13)
        | v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk4_2(X12,X13),X13)
        | v5_waybel_6(X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_6])])])])])])).

cnf(c_0_40,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( r2_hidden(k12_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_34]),c_0_35]),c_0_36]),c_0_25]),c_0_27]),c_0_15]),c_0_16])]),c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,X4,X1)
    | v2_struct_0(X2)
    | ~ v5_waybel_6(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,k11_lattice3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_16])]),c_0_22]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))),k5_waybel_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_34]),c_0_35]),c_0_36]),c_0_25]),c_0_27]),c_0_15]),c_0_16])]),c_0_37]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k12_lattice3(esk5_0,X1,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))) = k11_lattice3(esk5_0,X1,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36]),c_0_15]),c_0_16])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_34]),c_0_35]),c_0_36]),c_0_25]),c_0_27]),c_0_15]),c_0_16])]),c_0_37]),c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),X1)
    | r1_orders_2(esk5_0,X2,X1)
    | ~ r1_orders_2(esk5_0,k11_lattice3(esk5_0,X2,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))),X1)
    | ~ v5_waybel_6(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_16])]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v5_waybel_6(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk5_0,k12_lattice3(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k12_lattice3(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))) = k11_lattice3(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk6_0)
    | r1_orders_2(esk5_0,X1,esk6_0)
    | ~ r1_orders_2(esk5_0,k11_lattice3(esk5_0,X1,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_21])])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk5_0,k11_lattice3(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0))),esk6_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk5_0,esk6_0))
    | ~ r1_orders_2(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_16])]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk6_0)
    | r1_orders_2(esk5_0,esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),k5_waybel_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44])])).

cnf(c_0_61,plain,
    ( v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),k5_waybel_0(esk5_0,esk6_0))
    | r2_hidden(esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),k5_waybel_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_50])])).

cnf(c_0_63,plain,
    ( v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k5_waybel_0(esk5_0,esk6_0)),k5_waybel_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_31]),c_0_34]),c_0_35]),c_0_36]),c_0_25]),c_0_27]),c_0_15]),c_0_16])]),c_0_37]),c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31]),c_0_34]),c_0_35]),c_0_36]),c_0_25]),c_0_27]),c_0_15]),c_0_16])]),c_0_37]),c_0_38]),
    [proof]).

%------------------------------------------------------------------------------
