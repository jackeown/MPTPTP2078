%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 118 expanded)
%              Number of clauses        :   30 (  44 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 775 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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

cnf(c_0_16,plain,
    ( esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4) = X4
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_12]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2) = X2
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ l1_struct_0(X17)
      | ~ l1_waybel_0(X18,X17)
      | l1_orders_2(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1),u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))) = esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_35,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | ~ v1_xboole_0(u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_33])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.14/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.14/0.38  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.14/0.38  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.38  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X25, X26, X28]:(((((((m1_subset_1(esk2_5(X19,X20,X21,X22,X23),u1_struct_0(X20))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk2_5(X19,X20,X21,X22,X23)=X23|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk2_5(X19,X20,X21,X22,X23))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(~m1_subset_1(X26,u1_struct_0(X20))|X26!=X25|~r1_orders_2(X20,X21,X26)|r2_hidden(X25,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(u1_waybel_0(X19,X22)=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&((~r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|(~m1_subset_1(X28,u1_struct_0(X20))|X28!=esk3_4(X19,X20,X21,X22)|~r1_orders_2(X20,X21,X28))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(((m1_subset_1(esk4_4(X19,X20,X21,X22),u1_struct_0(X20))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk4_4(X19,X20,X21,X22)=esk3_4(X19,X20,X21,X22)|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk4_4(X19,X20,X21,X22))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X30, X31, X32]:((v6_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))&(l1_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.14/0.38  cnf(c_0_11, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((~v2_struct_0(esk6_0)&l1_waybel_0(esk6_0,esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.14/0.38  cnf(c_0_15, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_16, plain, (esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4)=X4|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12]), c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_21, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_12]), c_0_13])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2)=X2|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1)=X1|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  fof(c_0_30, plain, ![X17, X18]:(~l1_struct_0(X17)|(~l1_waybel_0(X18,X17)|l1_orders_2(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.14/0.38  fof(c_0_31, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1),u1_struct_0(esk6_0))|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  fof(c_0_34, plain, ![X16]:(~l1_orders_2(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.38  cnf(c_0_35, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  fof(c_0_36, plain, ![X15]:(v2_struct_0(X15)|~l1_struct_0(X15)|~v1_xboole_0(u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.38  cnf(c_0_37, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_33])).
% 0.14/0.38  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (l1_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_18])])).
% 0.14/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_20])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_25]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 47
% 0.14/0.38  # Proof object clause steps            : 30
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 21
% 0.14/0.38  # Proof object clause conjectures      : 18
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 21
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 25
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 25
% 0.14/0.38  # Processed clauses                    : 99
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 12
% 0.14/0.38  # ...remaining for further processing  : 87
% 0.14/0.38  # Other redundant clauses eliminated   : 8
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 129
% 0.14/0.38  # ...of the previous two non-trivial   : 112
% 0.14/0.38  # Contextual simplify-reflections      : 12
% 0.14/0.38  # Paramodulations                      : 120
% 0.14/0.38  # Factorizations                       : 2
% 0.14/0.38  # Equation resolutions                 : 8
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 53
% 0.14/0.38  #    Positive orientable unit clauses  : 15
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 35
% 0.14/0.38  # Current number of unprocessed clauses: 62
% 0.14/0.38  # ...number of literals in the above   : 260
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 27
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1959
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 221
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.14/0.38  # Unit Clause-clause subsumption calls : 21
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 7072
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.040 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
