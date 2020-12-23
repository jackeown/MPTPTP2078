%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 873 expanded)
%              Number of clauses        :   66 ( 303 expanded)
%              Number of leaves         :   12 ( 210 expanded)
%              Depth                    :   19
%              Number of atoms          :  507 (6410 expanded)
%              Number of equality atoms :   33 ( 145 expanded)
%              Maximal formula depth    :   24 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r2_lattice3(X15,X17,X16)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X17,X18)
        | r1_orders_2(X15,X16,X18)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_14,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & v5_waybel_6(esk5_0,esk4_0)
    & ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_hidden(X11,X9)
        | r1_orders_2(X8,X11,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))
        | r2_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r2_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,esk1_3(X8,X9,X10),X10)
        | r2_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | r1_orders_2(X5,X6,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_23,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_20])])).

cnf(c_0_26,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_20])])).

cnf(c_0_30,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_20]),c_0_28])])).

fof(c_0_36,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ v1_lattice3(X7)
      | ~ v2_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_37,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk1_3(esk4_0,X1,esk5_0),k5_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1)
    | r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_20])])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_20])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18])])).

cnf(c_0_42,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | v2_struct_0(esk4_0)
    | ~ r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))
    | v2_struct_0(esk4_0)
    | ~ r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))
    | m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

fof(c_0_55,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | m1_subset_1(k5_waybel_0(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_56,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_54]),c_0_44]),c_0_20])])).

fof(c_0_57,plain,(
    ! [X30,X31,X33] :
      ( ( ~ v1_xboole_0(esk3_2(X30,X31))
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( v1_waybel_0(esk3_2(X30,X31),X30)
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( v12_waybel_0(esk3_2(X30,X31),X30)
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( v1_waybel_7(esk3_2(X30,X31),X30)
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk3_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( X31 = k1_yellow_0(X30,esk3_2(X30,X31))
        | ~ v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) )
      & ( v1_xboole_0(X33)
        | ~ v1_waybel_0(X33,X30)
        | ~ v12_waybel_0(X33,X30)
        | ~ v1_waybel_7(X33,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | X31 != k1_yellow_0(X30,X33)
        | v4_waybel_7(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_58,plain,(
    ! [X13,X14] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(k1_yellow_0(X13,X14),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X34,X35] :
      ( ~ v3_orders_2(X34)
      | ~ v4_orders_2(X34)
      | ~ v5_orders_2(X34)
      | ~ v1_lattice3(X34)
      | ~ v2_lattice3(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ v5_waybel_6(X35,X34)
      | v1_waybel_7(k5_waybel_0(X34,X35),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r1_orders_2(esk4_0,esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),k5_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_56])).

cnf(c_0_62,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_18]),c_0_20])])).

cnf(c_0_65,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v5_waybel_6(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_69,plain,(
    ! [X25,X26] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25)) )
      & ( v1_waybel_0(k5_waybel_0(X25,X26),X25)
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_70,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v4_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | v12_waybel_0(k5_waybel_0(X23,X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_71,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_39])).

cnf(c_0_72,plain,
    ( v4_waybel_7(k1_yellow_0(X1,X2),X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_7(X2,X1)
    | ~ v2_lattice3(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_44]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_18]),c_0_66]),c_0_67]),c_0_68]),c_0_19]),c_0_44]),c_0_20]),c_0_28])])).

cnf(c_0_75,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_71]),c_0_44]),c_0_20])])).

cnf(c_0_78,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | ~ v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | ~ v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_67]),c_0_68]),c_0_19]),c_0_44]),c_0_20]),c_0_28])])).

cnf(c_0_79,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_18]),c_0_20]),c_0_28])])).

cnf(c_0_80,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_18]),c_0_68]),c_0_20])])).

cnf(c_0_81,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_77])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_18]),c_0_20]),c_0_28])])).

cnf(c_0_87,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_85]),c_0_44]),c_0_20])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_89]),c_0_44]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.41  # and selection function SelectNewComplexAHP.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t38_waybel_7, conjecture, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_waybel_7)).
% 0.20/0.41  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.20/0.41  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.20/0.41  fof(t17_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k5_waybel_0(X1,X2))<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_waybel_0)).
% 0.20/0.41  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.20/0.41  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.20/0.41  fof(dt_k5_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 0.20/0.41  fof(d6_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)<=>?[X3]:(((((~(v1_xboole_0(X3))&v1_waybel_0(X3,X1))&v12_waybel_0(X3,X1))&v1_waybel_7(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))&X2=k1_yellow_0(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_waybel_7)).
% 0.20/0.41  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.41  fof(t37_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v1_waybel_7(k5_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_waybel_7)).
% 0.20/0.41  fof(fc8_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k5_waybel_0(X1,X2)))&v1_waybel_0(k5_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_waybel_0)).
% 0.20/0.41  fof(fc12_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>v12_waybel_0(k5_waybel_0(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_waybel_0)).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ~(![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1))))), inference(assume_negation,[status(cth)],[t38_waybel_7])).
% 0.20/0.41  fof(c_0_13, plain, ![X15, X16, X17, X18, X19]:(((r2_lattice3(X15,X17,X16)|(X16!=k1_yellow_0(X15,X17)|~r1_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_lattice3(X15,X17,X18)|r1_orders_2(X15,X16,X18))|(X16!=k1_yellow_0(X15,X17)|~r1_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k1_yellow_0(X15,X19)|(m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k1_yellow_0(X15,X19)|(r2_lattice3(X15,X19,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(r2_lattice3(X15,X19,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&((X16=k1_yellow_0(X15,X19)|(~r1_orders_2(X15,X16,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(~r1_orders_2(X15,X16,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ((((((v3_orders_2(esk4_0)&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(v5_waybel_6(esk5_0,esk4_0)&~v4_waybel_7(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.41  fof(c_0_15, plain, ![X8, X9, X10, X11]:((~r2_lattice3(X8,X9,X10)|(~m1_subset_1(X11,u1_struct_0(X8))|(~r2_hidden(X11,X9)|r1_orders_2(X8,X11,X10)))|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&((m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))|r2_lattice3(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&((r2_hidden(esk1_3(X8,X9,X10),X9)|r2_lattice3(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&(~r1_orders_2(X8,esk1_3(X8,X9,X10),X10)|r2_lattice3(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.20/0.41  fof(c_0_16, plain, ![X27, X28, X29]:((~r2_hidden(X29,k5_waybel_0(X27,X28))|r1_orders_2(X27,X29,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~l1_orders_2(X27)))&(~r1_orders_2(X27,X29,X28)|r2_hidden(X29,k5_waybel_0(X27,X28))|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).
% 0.20/0.41  cnf(c_0_17, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_22, plain, ![X5, X6]:(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|r1_orders_2(X5,X6,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.20/0.41  cnf(c_0_23, plain, (r1_orders_2(X2,X1,X3)|v2_struct_0(X2)|~r2_hidden(X1,k5_waybel_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_26, plain, (r2_hidden(X2,k5_waybel_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_27, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk4_0,X1,esk5_0)|v2_struct_0(esk4_0)|~r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.41  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_32, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_33, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)|~r1_orders_2(esk4_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk5_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_20]), c_0_28])])).
% 0.20/0.41  fof(c_0_36, plain, ![X7]:(~l1_orders_2(X7)|(~v1_lattice3(X7)|~v2_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))|v2_struct_0(esk4_0)|~r2_hidden(esk1_3(esk4_0,X1,esk5_0),k5_waybel_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1)|r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|~r2_hidden(esk5_0,X2)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18])])).
% 0.20/0.41  cnf(c_0_42, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_24])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_45, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_46, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|v2_struct_0(esk4_0)|~r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_20])])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|~r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))|v2_struct_0(esk4_0)|~r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))|m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_25])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0))|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.20/0.41  fof(c_0_55, plain, ![X21, X22]:(v2_struct_0(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,u1_struct_0(X21))|m1_subset_1(k5_waybel_0(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_54]), c_0_44]), c_0_20])])).
% 0.20/0.41  fof(c_0_57, plain, ![X30, X31, X33]:(((((((~v1_xboole_0(esk3_2(X30,X31))|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30)))&(v1_waybel_0(esk3_2(X30,X31),X30)|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30))))&(v12_waybel_0(esk3_2(X30,X31),X30)|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30))))&(v1_waybel_7(esk3_2(X30,X31),X30)|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30))))&(m1_subset_1(esk3_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30))))&(X31=k1_yellow_0(X30,esk3_2(X30,X31))|~v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30))))&(v1_xboole_0(X33)|~v1_waybel_0(X33,X30)|~v12_waybel_0(X33,X30)|~v1_waybel_7(X33,X30)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))|X31!=k1_yellow_0(X30,X33)|v4_waybel_7(X31,X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~l1_orders_2(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).
% 0.20/0.41  fof(c_0_58, plain, ![X13, X14]:(~l1_orders_2(X13)|m1_subset_1(k1_yellow_0(X13,X14),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.41  cnf(c_0_59, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  fof(c_0_60, plain, ![X34, X35]:(~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~v1_lattice3(X34)|~v2_lattice3(X34)|~l1_orders_2(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|(~v5_waybel_6(X35,X34)|v1_waybel_7(k5_waybel_0(X34,X35),X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r1_orders_2(esk4_0,esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),esk5_0)|v2_struct_0(esk4_0)|~r2_hidden(esk1_3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0),k5_waybel_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_56])).
% 0.20/0.41  cnf(c_0_62, plain, (v1_xboole_0(X1)|v4_waybel_7(X3,X2)|~v1_waybel_0(X1,X2)|~v12_waybel_0(X1,X2)|~v1_waybel_7(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X3!=k1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_lattice3(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_63, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_18]), c_0_20])])).
% 0.20/0.41  cnf(c_0_65, plain, (v1_waybel_7(k5_waybel_0(X1,X2),X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_waybel_6(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (v5_waybel_6(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_69, plain, ![X25, X26]:((~v1_xboole_0(k5_waybel_0(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,u1_struct_0(X25))))&(v1_waybel_0(k5_waybel_0(X25,X26),X25)|(v2_struct_0(X25)|~v3_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,u1_struct_0(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).
% 0.20/0.41  fof(c_0_70, plain, ![X23, X24]:(v2_struct_0(X23)|~v4_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,u1_struct_0(X23))|v12_waybel_0(k5_waybel_0(X23,X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_39])).
% 0.20/0.41  cnf(c_0_72, plain, (v4_waybel_7(k1_yellow_0(X1,X2),X1)|v1_xboole_0(X2)|~v1_waybel_7(X2,X1)|~v2_lattice3(X1)|~v1_waybel_0(X2,X1)|~v12_waybel_0(X2,X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]), c_0_63])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_44]), c_0_20])])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_18]), c_0_66]), c_0_67]), c_0_68]), c_0_19]), c_0_44]), c_0_20]), c_0_28])])).
% 0.20/0.41  cnf(c_0_75, plain, (v1_waybel_0(k5_waybel_0(X1,X2),X1)|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_76, plain, (v2_struct_0(X1)|v12_waybel_0(k5_waybel_0(X1,X2),X1)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_71]), c_0_44]), c_0_20])])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|~v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|~v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_67]), c_0_68]), c_0_19]), c_0_44]), c_0_20]), c_0_28])])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_18]), c_0_20]), c_0_28])])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_18]), c_0_68]), c_0_20])])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_49, c_0_77])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_50, c_0_77])).
% 0.20/0.41  cnf(c_0_83, plain, (v2_struct_0(X1)|~v1_xboole_0(k5_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_81]), c_0_82])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_18]), c_0_20]), c_0_28])])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_85]), c_0_44]), c_0_20])])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (~v4_waybel_7(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (v2_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_89]), c_0_44]), c_0_20])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 91
% 0.20/0.41  # Proof object clause steps            : 66
% 0.20/0.41  # Proof object formula steps           : 25
% 0.20/0.41  # Proof object conjectures             : 50
% 0.20/0.41  # Proof object clause conjectures      : 47
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 27
% 0.20/0.41  # Proof object initial formulas used   : 12
% 0.20/0.41  # Proof object generating inferences   : 37
% 0.20/0.41  # Proof object simplifying inferences  : 82
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 12
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 38
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 38
% 0.20/0.41  # Processed clauses                    : 335
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 81
% 0.20/0.41  # ...remaining for further processing  : 254
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 18
% 0.20/0.41  # Backward-rewritten                   : 91
% 0.20/0.41  # Generated clauses                    : 436
% 0.20/0.41  # ...of the previous two non-trivial   : 451
% 0.20/0.41  # Contextual simplify-reflections      : 14
% 0.20/0.41  # Paramodulations                      : 433
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 104
% 0.20/0.41  #    Positive orientable unit clauses  : 14
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 89
% 0.20/0.41  # Current number of unprocessed clauses: 190
% 0.20/0.41  # ...number of literals in the above   : 787
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 147
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 6473
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1340
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 108
% 0.20/0.41  # Unit Clause-clause subsumption calls : 91
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 12
% 0.20/0.41  # BW rewrite match successes           : 7
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 18800
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.065 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
