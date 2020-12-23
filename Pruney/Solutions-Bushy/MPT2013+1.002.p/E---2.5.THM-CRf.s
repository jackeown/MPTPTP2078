%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2013+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (1823 expanded)
%              Number of clauses        :   59 ( 641 expanded)
%              Number of leaves         :    5 ( 438 expanded)
%              Depth                    :   15
%              Number of atoms          :  428 (12746 expanded)
%              Number of equality atoms :   65 (1895 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal clause size      :  110 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

fof(d7_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k4_waybel_9(X1,X2,X3)
                  <=> ( ! [X5] :
                          ( r2_hidden(X5,u1_struct_0(X4))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                              & X6 = X5
                              & r1_orders_2(X2,X3,X6) ) )
                      & r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4)))
                      & u1_waybel_0(X1,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(fraenkel_a_3_0_waybel_9,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2)
        & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
      <=> ? [X5] :
            ( m1_subset_1(X5,u1_struct_0(X3))
            & X1 = X5
            & r1_orders_2(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_waybel_9])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11,X13,X14,X16] :
      ( ( m1_subset_1(esk1_5(X7,X8,X9,X10,X11),u1_struct_0(X8))
        | ~ r2_hidden(X11,u1_struct_0(X10))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( esk1_5(X7,X8,X9,X10,X11) = X11
        | ~ r2_hidden(X11,u1_struct_0(X10))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( r1_orders_2(X8,X9,esk1_5(X7,X8,X9,X10,X11))
        | ~ r2_hidden(X11,u1_struct_0(X10))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X8))
        | X14 != X13
        | ~ r1_orders_2(X8,X9,X14)
        | r2_hidden(X13,u1_struct_0(X10))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( r2_relset_1(u1_struct_0(X10),u1_struct_0(X10),u1_orders_2(X10),k1_toler_1(u1_orders_2(X8),u1_struct_0(X10)))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( u1_waybel_0(X7,X10) = k2_partfun1(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),u1_struct_0(X10))
        | X10 != k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( ~ r2_hidden(esk2_4(X7,X8,X9,X10),u1_struct_0(X10))
        | ~ m1_subset_1(X16,u1_struct_0(X8))
        | X16 != esk2_4(X7,X8,X9,X10)
        | ~ r1_orders_2(X8,X9,X16)
        | ~ r2_relset_1(u1_struct_0(X10),u1_struct_0(X10),u1_orders_2(X10),k1_toler_1(u1_orders_2(X8),u1_struct_0(X10)))
        | u1_waybel_0(X7,X10) != k2_partfun1(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),u1_struct_0(X10))
        | X10 = k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( m1_subset_1(esk3_4(X7,X8,X9,X10),u1_struct_0(X8))
        | r2_hidden(esk2_4(X7,X8,X9,X10),u1_struct_0(X10))
        | ~ r2_relset_1(u1_struct_0(X10),u1_struct_0(X10),u1_orders_2(X10),k1_toler_1(u1_orders_2(X8),u1_struct_0(X10)))
        | u1_waybel_0(X7,X10) != k2_partfun1(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),u1_struct_0(X10))
        | X10 = k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( esk3_4(X7,X8,X9,X10) = esk2_4(X7,X8,X9,X10)
        | r2_hidden(esk2_4(X7,X8,X9,X10),u1_struct_0(X10))
        | ~ r2_relset_1(u1_struct_0(X10),u1_struct_0(X10),u1_orders_2(X10),k1_toler_1(u1_orders_2(X8),u1_struct_0(X10)))
        | u1_waybel_0(X7,X10) != k2_partfun1(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),u1_struct_0(X10))
        | X10 = k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( r1_orders_2(X8,X9,esk3_4(X7,X8,X9,X10))
        | r2_hidden(esk2_4(X7,X8,X9,X10),u1_struct_0(X10))
        | ~ r2_relset_1(u1_struct_0(X10),u1_struct_0(X10),u1_orders_2(X10),k1_toler_1(u1_orders_2(X8),u1_struct_0(X10)))
        | u1_waybel_0(X7,X10) != k2_partfun1(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),u1_struct_0(X10))
        | X10 = k4_waybel_9(X7,X8,X9)
        | ~ v6_waybel_0(X10,X7)
        | ~ l1_waybel_0(X10,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20] :
      ( ( v6_waybel_0(k4_waybel_9(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( l1_waybel_0(k4_waybel_9(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24,X26] :
      ( ( m1_subset_1(esk4_4(X21,X22,X23,X24),u1_struct_0(X23))
        | ~ r2_hidden(X21,a_3_0_waybel_9(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( X21 = esk4_4(X21,X22,X23,X24)
        | ~ r2_hidden(X21,a_3_0_waybel_9(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( r1_orders_2(X23,X24,esk4_4(X21,X22,X23,X24))
        | ~ r2_hidden(X21,a_3_0_waybel_9(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | X21 != X26
        | ~ r1_orders_2(X23,X24,X26)
        | r2_hidden(X21,a_3_0_waybel_9(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)) != a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,X2,esk1_5(X3,X1,X2,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X3,X1,X2)
    | ~ v6_waybel_0(X4,X3)
    | ~ l1_waybel_0(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = esk4_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( esk1_5(X1,X2,X3,X4,X5) = X5
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,esk4_4(X3,X4,X1,X2))
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_3_0_waybel_9(X4,X1,X2))
    | ~ l1_struct_0(X4)
    | ~ l1_waybel_0(X1,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,esk1_5(X3,X1,X2,k4_waybel_9(X3,X1,X2),X4))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X3,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk4_4(X1,esk6_0,esk7_0,X2) = X1
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ( ~ r2_hidden(esk5_2(X27,X28),X27)
        | ~ r2_hidden(esk5_2(X27,X28),X28)
        | X27 = X28 )
      & ( r2_hidden(esk5_2(X27,X28),X27)
        | r2_hidden(esk5_2(X27,X28),X28)
        | X27 = X28 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_26,plain,
    ( esk1_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4) = X4
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_11]),c_0_12])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_11]),c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk4_4(X2,esk6_0,esk7_0,X1))
    | ~ r2_hidden(X2,a_3_0_waybel_9(esk6_0,esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_4(X1,esk6_0,esk7_0,X2),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk1_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( esk4_4(X1,esk6_0,esk7_0,esk8_0) = X1
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(esk5_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( esk1_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2) = X2
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2),u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,u1_struct_0(X5))
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X1 != X3
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k4_waybel_9(X6,X2,X4)
    | ~ v6_waybel_0(X5,X6)
    | ~ l1_waybel_0(X5,X6)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X6)
    | ~ l1_struct_0(X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk4_4(X1,esk6_0,esk7_0,esk8_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_4(X1,esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1)
    | a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)) != a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,u1_struct_0(k4_waybel_9(X2,X3,X4)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])]),c_0_11]),c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r1_orders_2(esk7_0,esk8_0,esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0))
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),X1)
    | m1_subset_1(esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,a_3_0_waybel_9(X5,X2,X4))
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r1_orders_2(X2,X4,X1)
    | ~ l1_struct_0(X5)
    | ~ l1_waybel_0(X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_orders_2(esk7_0,esk8_0,esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r2_hidden(esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(X2,esk7_0,esk8_0)))
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(esk7_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24])]),c_0_16]),c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_orders_2(esk7_0,esk8_0,esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(esk5_2(X1,X2),X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r2_hidden(esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_15])]),c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(X1,esk7_0,esk8_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_24])]),c_0_16]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | r2_hidden(esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | ~ r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_14]),c_0_15])]),c_0_17]),c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) = X1
    | m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( X1 = u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))
    | r2_hidden(esk5_2(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),X1)
    | m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk4_4(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),a_3_0_waybel_9(X1,esk7_0,esk8_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_63]),c_0_24]),c_0_64])]),c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_14]),c_0_15])]),c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( esk1_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))) = esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk5_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_61]),c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).

%------------------------------------------------------------------------------
