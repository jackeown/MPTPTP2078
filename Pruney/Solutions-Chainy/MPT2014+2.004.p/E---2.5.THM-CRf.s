%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 119 expanded)
%              Number of clauses        :   31 (  45 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 ( 791 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal clause size      :  110 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(t13_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d1_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v2_struct_0(X1)
      <=> v1_xboole_0(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X28] :
      ( ( m1_subset_1(esk2_5(X19,X20,X21,X22,X23),u1_struct_0(X20))
        | ~ r2_hidden(X23,u1_struct_0(X22))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( esk2_5(X19,X20,X21,X22,X23) = X23
        | ~ r2_hidden(X23,u1_struct_0(X22))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( r1_orders_2(X20,X21,esk2_5(X19,X20,X21,X22,X23))
        | ~ r2_hidden(X23,u1_struct_0(X22))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X20))
        | X26 != X25
        | ~ r1_orders_2(X20,X21,X26)
        | r2_hidden(X25,u1_struct_0(X22))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( u1_waybel_0(X19,X22) = k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))
        | X22 != k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( ~ r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))
        | ~ m1_subset_1(X28,u1_struct_0(X20))
        | X28 != esk3_4(X19,X20,X21,X22)
        | ~ r1_orders_2(X20,X21,X28)
        | ~ r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))
        | u1_waybel_0(X19,X22) != k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))
        | X22 = k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( m1_subset_1(esk4_4(X19,X20,X21,X22),u1_struct_0(X20))
        | r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))
        | ~ r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))
        | u1_waybel_0(X19,X22) != k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))
        | X22 = k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( esk4_4(X19,X20,X21,X22) = esk3_4(X19,X20,X21,X22)
        | r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))
        | ~ r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))
        | u1_waybel_0(X19,X22) != k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))
        | X22 = k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( r1_orders_2(X20,X21,esk4_4(X19,X20,X21,X22))
        | r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))
        | ~ r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))
        | u1_waybel_0(X19,X22) != k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))
        | X22 = k4_waybel_9(X19,X20,X21)
        | ~ v6_waybel_0(X22,X19)
        | ~ l1_waybel_0(X22,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

fof(c_0_9,plain,(
    ! [X30,X31,X32] :
      ( ( v6_waybel_0(k4_waybel_9(X30,X31,X32),X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( l1_waybel_0(k4_waybel_9(X30,X31,X32),X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_waybel_9])).

cnf(c_0_11,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ~ r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ l1_struct_0(X16)
      | ~ l1_waybel_0(X17,X16)
      | l1_orders_2(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1),u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_31,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4) = X4
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_12]),c_0_13])).

fof(c_0_33,plain,(
    ! [X18] :
      ( ( ~ v2_struct_0(X18)
        | v1_xboole_0(u1_struct_0(X18))
        | ~ l1_struct_0(X18) )
      & ( ~ v1_xboole_0(u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2) = X2
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.41  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.041 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.20/0.41  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.20/0.41  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.41  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.41  fof(d1_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>(v2_struct_0(X1)<=>v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_struct_0)).
% 0.20/0.41  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X25, X26, X28]:(((((((m1_subset_1(esk2_5(X19,X20,X21,X22,X23),u1_struct_0(X20))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk2_5(X19,X20,X21,X22,X23)=X23|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk2_5(X19,X20,X21,X22,X23))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(~m1_subset_1(X26,u1_struct_0(X20))|X26!=X25|~r1_orders_2(X20,X21,X26)|r2_hidden(X25,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(u1_waybel_0(X19,X22)=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&((~r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|(~m1_subset_1(X28,u1_struct_0(X20))|X28!=esk3_4(X19,X20,X21,X22)|~r1_orders_2(X20,X21,X28))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(((m1_subset_1(esk4_4(X19,X20,X21,X22),u1_struct_0(X20))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk4_4(X19,X20,X21,X22)=esk3_4(X19,X20,X21,X22)|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk4_4(X19,X20,X21,X22))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.20/0.41  fof(c_0_9, plain, ![X30, X31, X32]:((v6_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))&(l1_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.20/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.20/0.41  cnf(c_0_11, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_12, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_13, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((~v2_struct_0(esk6_0)&l1_waybel_0(esk6_0,esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12]), c_0_13])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_20, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  fof(c_0_25, plain, ![X16, X17]:(~l1_struct_0(X16)|(~l1_waybel_0(X17,X16)|l1_orders_2(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.41  cnf(c_0_26, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  fof(c_0_27, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1),u1_struct_0(esk6_0))|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  fof(c_0_30, plain, ![X15]:(~l1_orders_2(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.41  cnf(c_0_31, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4)=X4|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_12]), c_0_13])).
% 0.20/0.41  fof(c_0_33, plain, ![X18]:((~v2_struct_0(X18)|v1_xboole_0(u1_struct_0(X18))|~l1_struct_0(X18))&(~v1_xboole_0(u1_struct_0(X18))|v2_struct_0(X18)|~l1_struct_0(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).
% 0.20/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (l1_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_16]), c_0_17])])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2)=X2|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.20/0.41  cnf(c_0_39, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1)=X1|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), c_0_19])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.20/0.41  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 48
% 0.20/0.41  # Proof object clause steps            : 31
% 0.20/0.41  # Proof object formula steps           : 17
% 0.20/0.41  # Proof object conjectures             : 22
% 0.20/0.41  # Proof object clause conjectures      : 19
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 16
% 0.20/0.41  # Proof object initial formulas used   : 8
% 0.20/0.41  # Proof object generating inferences   : 12
% 0.20/0.41  # Proof object simplifying inferences  : 21
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 29
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 29
% 0.20/0.41  # Processed clauses                    : 194
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 30
% 0.20/0.41  # ...remaining for further processing  : 164
% 0.20/0.41  # Other redundant clauses eliminated   : 8
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 18
% 0.20/0.41  # Generated clauses                    : 294
% 0.20/0.41  # ...of the previous two non-trivial   : 295
% 0.20/0.41  # Contextual simplify-reflections      : 12
% 0.20/0.41  # Paramodulations                      : 287
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 8
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
% 0.20/0.41  # Current number of processed clauses  : 110
% 0.20/0.41  #    Positive orientable unit clauses  : 15
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 3
% 0.20/0.41  #    Non-unit-clauses                  : 92
% 0.20/0.41  # Current number of unprocessed clauses: 150
% 0.20/0.41  # ...number of literals in the above   : 586
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 47
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4535
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 821
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 21
% 0.20/0.41  # Unit Clause-clause subsumption calls : 265
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 18
% 0.20/0.41  # BW rewrite match successes           : 4
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 14038
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.071 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.076 s
% 0.20/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
