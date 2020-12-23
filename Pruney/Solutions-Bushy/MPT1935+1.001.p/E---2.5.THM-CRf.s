%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   84 (3036 expanded)
%              Number of clauses        :   73 (1047 expanded)
%              Number of leaves         :    5 ( 734 expanded)
%              Depth                    :   18
%              Number of atoms          :  441 (32130 expanded)
%              Number of equality atoms :   43 (1607 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   49 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_yellow_6,conjecture,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) )
         => ( m3_yellow_6(X3,X1,X2)
          <=> ! [X4] :
                ( r2_hidden(X4,X1)
               => ( ~ v2_struct_0(k1_funct_1(X3,X4))
                  & v4_orders_2(k1_funct_1(X3,X4))
                  & v7_waybel_0(k1_funct_1(X3,X4))
                  & l1_waybel_0(k1_funct_1(X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_6)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(d15_yellow_6,axiom,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) )
         => ( m3_yellow_6(X3,X1,X2)
          <=> ! [X4] :
                ( r2_hidden(X4,k2_relat_1(X3))
               => ( ~ v2_struct_0(X4)
                  & v4_orders_2(X4)
                  & v7_waybel_0(X4)
                  & l1_waybel_0(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_yellow_6)).

fof(dt_m3_yellow_6,axiom,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( m3_yellow_6(X3,X1,X2)
         => ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m3_yellow_6)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( l1_struct_0(X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v4_relat_1(X3,X1)
              & v1_funct_1(X3)
              & v1_partfun1(X3,X1) )
           => ( m3_yellow_6(X3,X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => ( ~ v2_struct_0(k1_funct_1(X3,X4))
                    & v4_orders_2(k1_funct_1(X3,X4))
                    & v7_waybel_0(k1_funct_1(X3,X4))
                    & l1_waybel_0(k1_funct_1(X3,X4),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_yellow_6])).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ( ~ v1_partfun1(X11,X10)
        | k1_relat_1(X11) = X10
        | ~ v1_relat_1(X11)
        | ~ v4_relat_1(X11,X10) )
      & ( k1_relat_1(X11) != X10
        | v1_partfun1(X11,X10)
        | ~ v1_relat_1(X11)
        | ~ v4_relat_1(X11,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

fof(c_0_7,negated_conjecture,(
    ! [X29] :
      ( l1_struct_0(esk6_0)
      & v1_relat_1(esk7_0)
      & v4_relat_1(esk7_0,esk5_0)
      & v1_funct_1(esk7_0)
      & v1_partfun1(esk7_0,esk5_0)
      & ( r2_hidden(esk8_0,esk5_0)
        | ~ m3_yellow_6(esk7_0,esk5_0,esk6_0) )
      & ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
        | ~ v4_orders_2(k1_funct_1(esk7_0,esk8_0))
        | ~ v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
        | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0)
        | ~ m3_yellow_6(esk7_0,esk5_0,esk6_0) )
      & ( ~ v2_struct_0(k1_funct_1(esk7_0,X29))
        | ~ r2_hidden(X29,esk5_0)
        | m3_yellow_6(esk7_0,esk5_0,esk6_0) )
      & ( v4_orders_2(k1_funct_1(esk7_0,X29))
        | ~ r2_hidden(X29,esk5_0)
        | m3_yellow_6(esk7_0,esk5_0,esk6_0) )
      & ( v7_waybel_0(k1_funct_1(esk7_0,X29))
        | ~ r2_hidden(X29,esk5_0)
        | m3_yellow_6(esk7_0,esk5_0,esk6_0) )
      & ( l1_waybel_0(k1_funct_1(esk7_0,X29),esk6_0)
        | ~ r2_hidden(X29,esk5_0)
        | m3_yellow_6(esk7_0,esk5_0,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

cnf(c_0_8,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk7_0,X1),esk6_0)
    | m3_yellow_6(esk7_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,X1))
    | m3_yellow_6(esk7_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,X1))
    | m3_yellow_6(esk7_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( m3_yellow_6(esk7_0,esk5_0,esk6_0)
    | ~ v2_struct_0(k1_funct_1(esk7_0,X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk7_0,X1),esk6_0)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,X1))
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_13]),c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,X1))
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_13]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ v2_struct_0(k1_funct_1(esk7_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_13]),c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X2 != k2_relat_1(esk7_0)
    | ~ r2_hidden(esk2_3(esk7_0,X2,X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,esk2_3(esk7_0,X1,X2)))
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X1 != k2_relat_1(esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20]),c_0_11])])).

cnf(c_0_27,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,esk2_3(esk7_0,X1,X2)))
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X1 != k2_relat_1(esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_20]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X1 != k2_relat_1(esk7_0)
    | ~ v2_struct_0(X2)
    | ~ r2_hidden(esk2_3(esk7_0,X1,X2),k1_relat_1(esk7_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,esk5_0)
    | ~ m3_yellow_6(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_30,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v2_struct_0(X8)
        | ~ r2_hidden(X8,k2_relat_1(X7))
        | ~ m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) )
      & ( v4_orders_2(X8)
        | ~ r2_hidden(X8,k2_relat_1(X7))
        | ~ m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) )
      & ( v7_waybel_0(X8)
        | ~ r2_hidden(X8,k2_relat_1(X7))
        | ~ m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) )
      & ( l1_waybel_0(X8,X6)
        | ~ r2_hidden(X8,k2_relat_1(X7))
        | ~ m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) )
      & ( r2_hidden(esk1_3(X5,X6,X7),k2_relat_1(X7))
        | m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) )
      & ( v2_struct_0(esk1_3(X5,X6,X7))
        | ~ v4_orders_2(esk1_3(X5,X6,X7))
        | ~ v7_waybel_0(esk1_3(X5,X6,X7))
        | ~ l1_waybel_0(esk1_3(X5,X6,X7),X6)
        | m3_yellow_6(X7,X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v4_relat_1(X7,X5)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ l1_struct_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_yellow_6])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X2 != k2_relat_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_20]),c_0_11])])).

cnf(c_0_32,negated_conjecture,
    ( v4_orders_2(X1)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X2 != k2_relat_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_33,negated_conjecture,
    ( v7_waybel_0(X1)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X2 != k2_relat_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_34,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | X1 != k2_relat_1(esk7_0)
    | ~ v2_struct_0(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_20]),c_0_11])])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( ( v1_relat_1(X24)
        | ~ m3_yellow_6(X24,X22,X23)
        | ~ l1_struct_0(X23) )
      & ( v4_relat_1(X24,X22)
        | ~ m3_yellow_6(X24,X22,X23)
        | ~ l1_struct_0(X23) )
      & ( v1_funct_1(X24)
        | ~ m3_yellow_6(X24,X22,X23)
        | ~ l1_struct_0(X23) )
      & ( v1_partfun1(X24,X22)
        | ~ m3_yellow_6(X24,X22,X23)
        | ~ l1_struct_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m3_yellow_6])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk7_0))
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_13]),c_0_13])).

cnf(c_0_38,plain,
    ( v2_struct_0(esk1_3(X1,X2,X3))
    | m3_yellow_6(X3,X1,X2)
    | ~ v4_orders_2(esk1_3(X1,X2,X3))
    | ~ v7_waybel_0(esk1_3(X1,X2,X3))
    | ~ l1_waybel_0(esk1_3(X1,X2,X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( v4_orders_2(X1)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v7_waybel_0(X1)
    | m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ v2_struct_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v7_waybel_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v1_funct_1(X1)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( v1_partfun1(X1,X2)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X1 != k1_funct_1(esk7_0,esk8_0)
    | X2 != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_11])])).

cnf(c_0_50,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | m3_yellow_6(X1,X2,esk6_0)
    | ~ r2_hidden(esk1_3(X2,esk6_0,X1),k2_relat_1(esk7_0))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k2_relat_1(X3))
    | m3_yellow_6(X3,X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,plain,
    ( v7_waybel_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk8_0),X1)
    | X1 != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | m3_yellow_6(esk7_0,X1,esk6_0)
    | ~ v1_partfun1(esk7_0,X1)
    | ~ v4_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_20]),c_0_11]),c_0_40])])).

cnf(c_0_56,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_1(esk7_0,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_58,plain,
    ( v4_orders_2(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ v4_orders_2(k1_funct_1(esk7_0,esk8_0))
    | ~ v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
    | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0)
    | ~ m3_yellow_6(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_60,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
    | k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_11])])).

cnf(c_0_62,plain,
    ( v4_orders_2(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_58,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_63,plain,
    ( l1_waybel_0(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(X3))
    | ~ m3_yellow_6(X3,X4,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X4)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0)
    | ~ v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
    | ~ v4_orders_2(k1_funct_1(esk7_0,esk8_0))
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_13])).

cnf(c_0_65,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
    | k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,esk8_0))
    | k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_67,plain,
    ( l1_waybel_0(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(X3))
    | ~ m3_yellow_6(X3,X4,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_63,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_68,plain,
    ( ~ v2_struct_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0)
    | ~ v7_waybel_0(k1_funct_1(esk7_0,esk8_0))
    | ~ v4_orders_2(k1_funct_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_61])])).

cnf(c_0_70,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_40])])).

cnf(c_0_71,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,esk8_0))
    | k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_61])])).

cnf(c_0_72,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk7_0,esk8_0),X1)
    | k2_relat_1(X2) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m3_yellow_6(X2,X3,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_54])).

cnf(c_0_73,plain,
    ( ~ v2_struct_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_68,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0)
    | ~ v4_orders_2(k1_funct_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_40])])).

cnf(c_0_76,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk7_0,esk8_0),X1)
    | k2_relat_1(X2) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(X2,X3,X1)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_61])])).

cnf(c_0_77,negated_conjecture,
    ( k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ m3_yellow_6(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk7_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_61]),c_0_40])])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ v2_struct_0(k1_funct_1(esk7_0,esk8_0))
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(X1) != k2_relat_1(esk7_0)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_61]),c_0_40])]),
    [proof]).

%------------------------------------------------------------------------------
