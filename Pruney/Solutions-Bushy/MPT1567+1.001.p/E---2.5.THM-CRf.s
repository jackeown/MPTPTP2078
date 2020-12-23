%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1567+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 (  63 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  161 ( 327 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(t45_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_0)).

fof(t43_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( r1_lattice3(X8,X10,X9)
        | X9 != k2_yellow_0(X8,X10)
        | ~ r2_yellow_0(X8,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r1_lattice3(X8,X10,X11)
        | r1_orders_2(X8,X11,X9)
        | X9 != k2_yellow_0(X8,X10)
        | ~ r2_yellow_0(X8,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( X9 = k2_yellow_0(X8,X12)
        | m1_subset_1(esk1_3(X8,X9,X12),u1_struct_0(X8))
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_yellow_0(X8,X12)
        | m1_subset_1(esk1_3(X8,X9,X12),u1_struct_0(X8))
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( X9 = k2_yellow_0(X8,X12)
        | r1_lattice3(X8,X12,esk1_3(X8,X9,X12))
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_yellow_0(X8,X12)
        | r1_lattice3(X8,X12,esk1_3(X8,X9,X12))
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( X9 = k2_yellow_0(X8,X12)
        | ~ r1_orders_2(X8,esk1_3(X8,X9,X12),X9)
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_yellow_0(X8,X12)
        | ~ r1_orders_2(X8,esk1_3(X8,X9,X12),X9)
        | ~ r1_lattice3(X8,X12,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(X6)
      | m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_0])).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v5_orders_2(esk2_0)
    & v2_yellow_0(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ r1_orders_2(esk2_0,esk3_0,k4_yellow_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_12,plain,(
    ! [X14] :
      ( ( r2_yellow_0(X14,k1_xboole_0)
        | v2_struct_0(X14)
        | ~ v5_orders_2(X14)
        | ~ v2_yellow_0(X14)
        | ~ l1_orders_2(X14) )
      & ( r1_yellow_0(X14,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ v5_orders_2(X14)
        | ~ v2_yellow_0(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_yellow_0])])])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ( r2_lattice3(X15,k1_xboole_0,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r1_lattice3(X15,k1_xboole_0,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_14,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | k4_yellow_0(X5) = k2_yellow_0(X5,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v2_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k2_yellow_0(esk2_0,X2))
    | ~ r1_lattice3(esk2_0,X2,X1)
    | ~ r2_yellow_0(esk2_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( r2_yellow_0(esk2_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16]),c_0_17])]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(esk2_0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk3_0,k4_yellow_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k4_yellow_0(esk2_0) = k2_yellow_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k2_yellow_0(esk2_0,k1_xboole_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk3_0,k2_yellow_0(esk2_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
