%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:34 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  102 (18512 expanded)
%              Number of clauses        :   89 (6814 expanded)
%              Number of leaves         :    6 (4468 expanded)
%              Depth                    :   36
%              Number of atoms          :  500 (123229 expanded)
%              Number of equality atoms :   69 (18170 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal clause size      :  110 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18,X19,X21,X22,X24] :
      ( ( m1_subset_1(esk2_5(X15,X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r2_hidden(X19,u1_struct_0(X18))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( esk2_5(X15,X16,X17,X18,X19) = X19
        | ~ r2_hidden(X19,u1_struct_0(X18))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( r1_orders_2(X16,X17,esk2_5(X15,X16,X17,X18,X19))
        | ~ r2_hidden(X19,u1_struct_0(X18))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X16))
        | X22 != X21
        | ~ r1_orders_2(X16,X17,X22)
        | r2_hidden(X21,u1_struct_0(X18))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( u1_waybel_0(X15,X18) = k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))
        | X18 != k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))
        | ~ m1_subset_1(X24,u1_struct_0(X16))
        | X24 != esk3_4(X15,X16,X17,X18)
        | ~ r1_orders_2(X16,X17,X24)
        | ~ r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))
        | u1_waybel_0(X15,X18) != k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))
        | X18 = k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( m1_subset_1(esk4_4(X15,X16,X17,X18),u1_struct_0(X16))
        | r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))
        | ~ r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))
        | u1_waybel_0(X15,X18) != k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))
        | X18 = k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( esk4_4(X15,X16,X17,X18) = esk3_4(X15,X16,X17,X18)
        | r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))
        | ~ r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))
        | u1_waybel_0(X15,X18) != k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))
        | X18 = k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( r1_orders_2(X16,X17,esk4_4(X15,X16,X17,X18))
        | r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))
        | ~ r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))
        | u1_waybel_0(X15,X18) != k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))
        | X18 = k4_waybel_9(X15,X16,X17)
        | ~ v6_waybel_0(X18,X15)
        | ~ l1_waybel_0(X18,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

fof(c_0_8,plain,(
    ! [X26,X27,X28] :
      ( ( v6_waybel_0(k4_waybel_9(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( l1_waybel_0(k4_waybel_9(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_9,plain,(
    ! [X29,X30,X31,X32,X34] :
      ( ( m1_subset_1(esk5_4(X29,X30,X31,X32),u1_struct_0(X31))
        | ~ r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( X29 = esk5_4(X29,X30,X31,X32)
        | ~ r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( r1_orders_2(X31,X32,esk5_4(X29,X30,X31,X32))
        | ~ r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( ~ m1_subset_1(X34,u1_struct_0(X31))
        | X29 != X34
        | ~ r1_orders_2(X31,X32,X34)
        | r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)) != a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,esk2_5(X3,X1,X2,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X3,X1,X2)
    | ~ v6_waybel_0(X4,X3)
    | ~ l1_waybel_0(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( X1 = esk5_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,esk2_5(X3,X1,X2,k4_waybel_9(X3,X1,X2),X4))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X3,X1,X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( esk5_4(X1,esk6_0,esk7_0,X2) = X1
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4) = X4
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_14]),c_0_15])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_14]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( esk5_4(X1,esk6_0,esk7_0,esk8_0) = X1
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2) = X2
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18])]),c_0_20]),c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_18])]),c_0_20]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1)
    | X1 = a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)
    | r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)) != a_3_0_waybel_9(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,a_3_0_waybel_9(X5,X2,X4))
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r1_orders_2(X2,X4,X1)
    | ~ l1_struct_0(X5)
    | ~ l1_waybel_0(X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))
    | esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,a_3_0_waybel_9(X1,X2,X4))
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_48,plain,
    ( r1_orders_2(X1,X2,esk5_4(X3,X4,X1,X2))
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_3_0_waybel_9(X4,X1,X2))
    | ~ l1_struct_0(X4)
    | ~ l1_waybel_0(X1,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])]),c_0_19]),c_0_47])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk5_4(X2,esk6_0,esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(esk6_0,esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_17]),c_0_18])]),c_0_20]),c_0_19])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk5_4(X1,esk6_0,esk7_0,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk5_4(X1,esk6_0,esk7_0,esk8_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_4(X1,esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_59,negated_conjecture,
    ( X1 = a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)
    | r1_orders_2(esk7_0,esk8_0,esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0))
    | r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0) = esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_56]),c_0_38]),c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)) = X1
    | m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),X1)),u1_struct_0(esk7_0))
    | r2_hidden(esk1_2(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( X1 = a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,u1_struct_0(k4_waybel_9(X1,X2,X4)))
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])]),c_0_14]),c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0))
    | m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_62]),c_0_38])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))
    | ~ m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_27])]),c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))
    | m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_62]),c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))
    | m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | ~ m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))
    | m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_69]),c_0_27])]),c_0_19]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))))
    | m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_62]),c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))
    | r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))))
    | m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_77]),c_0_38]),c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_78]),c_0_38]),c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_82]),c_0_27]),c_0_83])]),c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_86]),c_0_38])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_87]),c_0_60])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_88])])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))
    | r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_90]),c_0_38])).

cnf(c_0_92,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_91]),c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_92]),c_0_27]),c_0_83])]),c_0_19])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_95]),c_0_38])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_96]),c_0_60])).

cnf(c_0_98,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_97]),c_0_27]),c_0_88])]),c_0_19])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_95]),c_0_38])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.51/0.69  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.51/0.69  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.51/0.69  #
% 0.51/0.69  # Preprocessing time       : 0.028 s
% 0.51/0.69  # Presaturation interreduction done
% 0.51/0.69  
% 0.51/0.69  # Proof found!
% 0.51/0.69  # SZS status Theorem
% 0.51/0.69  # SZS output start CNFRefutation
% 0.51/0.69  fof(t12_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_waybel_9)).
% 0.51/0.69  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.51/0.69  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.51/0.69  fof(fraenkel_a_3_0_waybel_9, axiom, ![X1, X2, X3, X4]:(((((~(v2_struct_0(X2))&l1_struct_0(X2))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X2))&m1_subset_1(X4,u1_struct_0(X3)))=>(r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))<=>?[X5]:((m1_subset_1(X5,u1_struct_0(X3))&X1=X5)&r1_orders_2(X3,X4,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 0.51/0.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.51/0.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.51/0.69  fof(c_0_6, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3))))), inference(assume_negation,[status(cth)],[t12_waybel_9])).
% 0.51/0.69  fof(c_0_7, plain, ![X15, X16, X17, X18, X19, X21, X22, X24]:(((((((m1_subset_1(esk2_5(X15,X16,X17,X18,X19),u1_struct_0(X16))|~r2_hidden(X19,u1_struct_0(X18))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(esk2_5(X15,X16,X17,X18,X19)=X19|~r2_hidden(X19,u1_struct_0(X18))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&(r1_orders_2(X16,X17,esk2_5(X15,X16,X17,X18,X19))|~r2_hidden(X19,u1_struct_0(X18))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&(~m1_subset_1(X22,u1_struct_0(X16))|X22!=X21|~r1_orders_2(X16,X17,X22)|r2_hidden(X21,u1_struct_0(X18))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&(r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&(u1_waybel_0(X15,X18)=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))|X18!=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&((~r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))|(~m1_subset_1(X24,u1_struct_0(X16))|X24!=esk3_4(X15,X16,X17,X18)|~r1_orders_2(X16,X17,X24))|~r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))|u1_waybel_0(X15,X18)!=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))|X18=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(((m1_subset_1(esk4_4(X15,X16,X17,X18),u1_struct_0(X16))|r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))|~r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))|u1_waybel_0(X15,X18)!=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))|X18=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(esk4_4(X15,X16,X17,X18)=esk3_4(X15,X16,X17,X18)|r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))|~r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))|u1_waybel_0(X15,X18)!=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))|X18=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&(r1_orders_2(X16,X17,esk4_4(X15,X16,X17,X18))|r2_hidden(esk3_4(X15,X16,X17,X18),u1_struct_0(X18))|~r2_relset_1(u1_struct_0(X18),u1_struct_0(X18),u1_orders_2(X18),k1_toler_1(u1_orders_2(X16),u1_struct_0(X18)))|u1_waybel_0(X15,X18)!=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),u1_waybel_0(X15,X16),u1_struct_0(X18))|X18=k4_waybel_9(X15,X16,X17)|(~v6_waybel_0(X18,X15)|~l1_waybel_0(X18,X15))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.51/0.69  fof(c_0_8, plain, ![X26, X27, X28]:((v6_waybel_0(k4_waybel_9(X26,X27,X28),X26)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~l1_waybel_0(X27,X26)|~m1_subset_1(X28,u1_struct_0(X27))))&(l1_waybel_0(k4_waybel_9(X26,X27,X28),X26)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~l1_waybel_0(X27,X26)|~m1_subset_1(X28,u1_struct_0(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.51/0.69  fof(c_0_9, plain, ![X29, X30, X31, X32, X34]:((((m1_subset_1(esk5_4(X29,X30,X31,X32),u1_struct_0(X31))|~r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))&(X29=esk5_4(X29,X30,X31,X32)|~r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31)))))&(r1_orders_2(X31,X32,esk5_4(X29,X30,X31,X32))|~r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31)))))&(~m1_subset_1(X34,u1_struct_0(X31))|X29!=X34|~r1_orders_2(X31,X32,X34)|r2_hidden(X29,a_3_0_waybel_9(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).
% 0.51/0.69  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((~v2_struct_0(esk7_0)&l1_waybel_0(esk7_0,esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))!=a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.51/0.69  fof(c_0_11, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.51/0.69  fof(c_0_12, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.51/0.69  cnf(c_0_13, plain, (r1_orders_2(X1,X2,esk2_5(X3,X1,X2,X4,X5))|v2_struct_0(X1)|v2_struct_0(X3)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X3,X1,X2)|~v6_waybel_0(X4,X3)|~l1_waybel_0(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X1,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.51/0.69  cnf(c_0_14, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.51/0.69  cnf(c_0_15, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.51/0.69  cnf(c_0_16, plain, (X1=esk5_4(X1,X2,X3,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.51/0.69  cnf(c_0_17, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_18, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_21, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.51/0.69  cnf(c_0_23, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.51/0.69  cnf(c_0_24, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.51/0.69  cnf(c_0_25, plain, (r1_orders_2(X1,X2,esk2_5(X3,X1,X2,k4_waybel_9(X3,X1,X2),X4))|v2_struct_0(X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X1,X3)|~l1_struct_0(X3)|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X3,X1,X2)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14]), c_0_15])).
% 0.51/0.69  cnf(c_0_26, negated_conjecture, (esk5_4(X1,esk6_0,esk7_0,X2)=X1|~m1_subset_1(X2,u1_struct_0(esk7_0))|~r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.51/0.69  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_28, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.51/0.69  cnf(c_0_29, plain, (esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4)=X4|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_14]), c_0_15])).
% 0.51/0.69  cnf(c_0_30, plain, (m1_subset_1(esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_14]), c_0_15])).
% 0.51/0.69  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk7_0,X1,esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.51/0.69  cnf(c_0_32, negated_conjecture, (esk5_4(X1,esk6_0,esk7_0,esk8_0)=X1|~r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.51/0.69  cnf(c_0_33, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.51/0.69  cnf(c_0_34, negated_conjecture, (esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2)=X2|~m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_18])]), c_0_20]), c_0_19])).
% 0.51/0.69  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,X1,k4_waybel_9(esk6_0,esk7_0,X1),X2),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_17]), c_0_18])]), c_0_20]), c_0_19])).
% 0.51/0.69  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1))|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.51/0.69  cnf(c_0_37, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1)|X1=a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)|r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.51/0.69  cnf(c_0_38, negated_conjecture, (u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))!=a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.51/0.69  cnf(c_0_39, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1)=X1|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.51/0.69  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),X1),u1_struct_0(esk7_0))|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.51/0.69  cnf(c_0_41, plain, (r2_hidden(X3,a_3_0_waybel_9(X5,X2,X4))|v2_struct_0(X5)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r1_orders_2(X2,X4,X1)|~l1_struct_0(X5)|~l1_waybel_0(X2,X5)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.51/0.69  cnf(c_0_42, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.51/0.69  cnf(c_0_43, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))|esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_38])).
% 0.51/0.69  cnf(c_0_44, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_38])).
% 0.51/0.69  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,a_3_0_waybel_9(X1,X2,X4))|~r1_orders_2(X2,X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(er,[status(thm)],[c_0_41])).
% 0.51/0.69  cnf(c_0_46, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.51/0.69  cnf(c_0_47, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.51/0.69  cnf(c_0_48, plain, (r1_orders_2(X1,X2,esk5_4(X3,X4,X1,X2))|v2_struct_0(X4)|v2_struct_0(X1)|~r2_hidden(X3,a_3_0_waybel_9(X4,X1,X2))|~l1_struct_0(X4)|~l1_waybel_0(X1,X4)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.51/0.69  cnf(c_0_49, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|v2_struct_0(X1)|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])]), c_0_19]), c_0_47])).
% 0.51/0.69  cnf(c_0_50, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),u1_struct_0(X3))|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.51/0.69  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk7_0,X1,esk5_4(X2,esk6_0,esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(X2,a_3_0_waybel_9(esk6_0,esk7_0,X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_17]), c_0_18])]), c_0_20]), c_0_19])).
% 0.51/0.69  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.51/0.69  cnf(c_0_53, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk5_4(X1,esk6_0,esk7_0,X2),u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.51/0.69  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk5_4(X1,esk6_0,esk7_0,esk8_0))|~r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 0.51/0.69  cnf(c_0_56, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.51/0.69  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_4(X1,esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))|~r2_hidden(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_54, c_0_27])).
% 0.51/0.69  cnf(c_0_58, plain, (r2_hidden(X3,u1_struct_0(X5))|v2_struct_0(X2)|v2_struct_0(X6)|~m1_subset_1(X1,u1_struct_0(X2))|X1!=X3|~r1_orders_2(X2,X4,X1)|X5!=k4_waybel_9(X6,X2,X4)|~v6_waybel_0(X5,X6)|~l1_waybel_0(X5,X6)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X6)|~l1_struct_0(X6)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.51/0.69  cnf(c_0_59, negated_conjecture, (X1=a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)|r1_orders_2(esk7_0,esk8_0,esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0))|r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 0.51/0.69  cnf(c_0_60, negated_conjecture, (esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0)=esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_56]), c_0_38]), c_0_32])).
% 0.51/0.69  cnf(c_0_61, negated_conjecture, (u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))=X1|m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),X1)),u1_struct_0(esk7_0))|r2_hidden(esk1_2(X1,u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),X1)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.51/0.69  cnf(c_0_62, negated_conjecture, (X1=a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)|m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),X1),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))|r2_hidden(esk1_2(X1,a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.51/0.69  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,u1_struct_0(k4_waybel_9(X1,X2,X4)))|~r1_orders_2(X2,X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])]), c_0_14]), c_0_15])).
% 0.51/0.69  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_38])).
% 0.51/0.69  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0))|m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_38])).
% 0.51/0.69  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_62]), c_0_38])).
% 0.51/0.69  cnf(c_0_67, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))|~m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_27])]), c_0_19])).
% 0.51/0.69  cnf(c_0_68, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))|m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_62]), c_0_38])).
% 0.51/0.69  cnf(c_0_69, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))|m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_65, c_0_60])).
% 0.51/0.69  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_66, c_0_60])).
% 0.51/0.69  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|~m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_72, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))|m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_68, c_0_60])).
% 0.51/0.69  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|v2_struct_0(X1)|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_69]), c_0_27])]), c_0_19]), c_0_70])).
% 0.51/0.69  cnf(c_0_74, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_39])).
% 0.51/0.69  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_76, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))))|m1_subset_1(esk5_4(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_62]), c_0_38])).
% 0.51/0.69  cnf(c_0_77, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))|r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_74])).
% 0.51/0.69  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_75])).
% 0.51/0.69  cnf(c_0_79, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))))|m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_76, c_0_60])).
% 0.51/0.69  cnf(c_0_80, negated_conjecture, (esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_77]), c_0_38]), c_0_39])).
% 0.51/0.69  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk2_5(esk6_0,esk7_0,esk8_0,k4_waybel_9(esk6_0,esk7_0,esk8_0),esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_78]), c_0_38]), c_0_40])).
% 0.51/0.69  cnf(c_0_82, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))|m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.51/0.69  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_81, c_0_80])).
% 0.51/0.69  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|v2_struct_0(X1)|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_82]), c_0_27]), c_0_83])]), c_0_19])).
% 0.51/0.69  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_85])).
% 0.51/0.69  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_86]), c_0_38])).
% 0.51/0.69  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_87]), c_0_60])])).
% 0.51/0.69  cnf(c_0_89, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_88])])).
% 0.51/0.69  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))|r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_89])).
% 0.51/0.69  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_90]), c_0_38])).
% 0.51/0.69  cnf(c_0_92, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_91]), c_0_80])).
% 0.51/0.69  cnf(c_0_93, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(X1,esk7_0,esk8_0))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_92]), c_0_27]), c_0_83])]), c_0_19])).
% 0.51/0.69  cnf(c_0_94, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_95, negated_conjecture, (r1_tarski(u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_94])).
% 0.51/0.69  cnf(c_0_96, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),a_3_0_waybel_9(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_95]), c_0_38])).
% 0.51/0.69  cnf(c_0_97, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_96]), c_0_60])).
% 0.51/0.69  cnf(c_0_98, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(X1,esk7_0,esk8_0)))|~l1_waybel_0(esk7_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_97]), c_0_27]), c_0_88])]), c_0_19])).
% 0.51/0.69  cnf(c_0_99, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0))),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_17]), c_0_18])]), c_0_20])).
% 0.51/0.69  cnf(c_0_100, negated_conjecture, (~r1_tarski(a_3_0_waybel_9(esk6_0,esk7_0,esk8_0),u1_struct_0(k4_waybel_9(esk6_0,esk7_0,esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_95]), c_0_38])).
% 0.51/0.69  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_99]), c_0_100]), ['proof']).
% 0.51/0.69  # SZS output end CNFRefutation
% 0.51/0.69  # Proof object total steps             : 102
% 0.51/0.69  # Proof object clause steps            : 89
% 0.51/0.69  # Proof object formula steps           : 13
% 0.51/0.69  # Proof object conjectures             : 72
% 0.51/0.69  # Proof object clause conjectures      : 69
% 0.51/0.69  # Proof object formula conjectures     : 3
% 0.51/0.69  # Proof object initial clauses used    : 19
% 0.51/0.69  # Proof object initial formulas used   : 6
% 0.51/0.69  # Proof object generating inferences   : 58
% 0.51/0.69  # Proof object simplifying inferences  : 111
% 0.51/0.69  # Training examples: 0 positive, 0 negative
% 0.51/0.69  # Parsed axioms                        : 6
% 0.51/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.69  # Initial clauses                      : 28
% 0.51/0.69  # Removed in clause preprocessing      : 0
% 0.51/0.69  # Initial clauses in saturation        : 28
% 0.51/0.69  # Processed clauses                    : 673
% 0.51/0.69  # ...of these trivial                  : 10
% 0.51/0.69  # ...subsumed                          : 301
% 0.51/0.69  # ...remaining for further processing  : 362
% 0.51/0.69  # Other redundant clauses eliminated   : 11
% 0.51/0.69  # Clauses deleted for lack of memory   : 0
% 0.51/0.69  # Backward-subsumed                    : 12
% 0.51/0.69  # Backward-rewritten                   : 91
% 0.51/0.69  # Generated clauses                    : 14494
% 0.51/0.69  # ...of the previous two non-trivial   : 13706
% 0.51/0.69  # Contextual simplify-reflections      : 36
% 0.51/0.69  # Paramodulations                      : 14396
% 0.51/0.69  # Factorizations                       : 88
% 0.51/0.69  # Equation resolutions                 : 11
% 0.51/0.69  # Propositional unsat checks           : 0
% 0.51/0.69  #    Propositional check models        : 0
% 0.51/0.69  #    Propositional check unsatisfiable : 0
% 0.51/0.69  #    Propositional clauses             : 0
% 0.51/0.69  #    Propositional clauses after purity: 0
% 0.51/0.69  #    Propositional unsat core size     : 0
% 0.51/0.69  #    Propositional preprocessing time  : 0.000
% 0.51/0.69  #    Propositional encoding time       : 0.000
% 0.51/0.69  #    Propositional solver time         : 0.000
% 0.51/0.69  #    Success case prop preproc time    : 0.000
% 0.51/0.69  #    Success case prop encoding time   : 0.000
% 0.51/0.69  #    Success case prop solver time     : 0.000
% 0.51/0.69  # Current number of processed clauses  : 222
% 0.51/0.69  #    Positive orientable unit clauses  : 24
% 0.51/0.69  #    Positive unorientable unit clauses: 0
% 0.51/0.69  #    Negative unit clauses             : 4
% 0.51/0.69  #    Non-unit-clauses                  : 194
% 0.51/0.69  # Current number of unprocessed clauses: 12998
% 0.51/0.69  # ...number of literals in the above   : 79361
% 0.51/0.69  # Current number of archived formulas  : 0
% 0.51/0.69  # Current number of archived clauses   : 130
% 0.51/0.69  # Clause-clause subsumption calls (NU) : 20182
% 0.51/0.69  # Rec. Clause-clause subsumption calls : 7759
% 0.51/0.69  # Non-unit clause-clause subsumptions  : 346
% 0.51/0.69  # Unit Clause-clause subsumption calls : 766
% 0.51/0.69  # Rewrite failures with RHS unbound    : 0
% 0.51/0.69  # BW rewrite match attempts            : 85
% 0.51/0.69  # BW rewrite match successes           : 10
% 0.51/0.69  # Condensation attempts                : 0
% 0.51/0.69  # Condensation successes               : 0
% 0.51/0.69  # Termbank termtop insertions          : 515892
% 0.51/0.70  
% 0.51/0.70  # -------------------------------------------------
% 0.51/0.70  # User time                : 0.336 s
% 0.51/0.70  # System time              : 0.009 s
% 0.51/0.70  # Total time               : 0.345 s
% 0.51/0.70  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
