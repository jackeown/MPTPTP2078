%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 118 expanded)
%              Number of clauses        :   30 (  44 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  282 ( 778 expanded)
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

fof(d1_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v2_struct_0(X1)
      <=> v1_xboole_0(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

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
    ! [X16,X17] :
      ( ~ l1_struct_0(X16)
      | ~ l1_waybel_0(X17,X16)
      | l1_orders_2(X17) ) ),
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
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_35,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X18] :
      ( ( ~ v2_struct_0(X18)
        | v1_xboole_0(u1_struct_0(X18))
        | ~ l1_struct_0(X18) )
      & ( ~ v1_xboole_0(u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).

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
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.36  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.028 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.13/0.36  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.13/0.36  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.13/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.36  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.13/0.36  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.36  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.36  fof(d1_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>(v2_struct_0(X1)<=>v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 0.13/0.36  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X25, X26, X28]:(((((((m1_subset_1(esk2_5(X19,X20,X21,X22,X23),u1_struct_0(X20))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk2_5(X19,X20,X21,X22,X23)=X23|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk2_5(X19,X20,X21,X22,X23))|~r2_hidden(X23,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(~m1_subset_1(X26,u1_struct_0(X20))|X26!=X25|~r1_orders_2(X20,X21,X26)|r2_hidden(X25,u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(u1_waybel_0(X19,X22)=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22!=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&((~r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|(~m1_subset_1(X28,u1_struct_0(X20))|X28!=esk3_4(X19,X20,X21,X22)|~r1_orders_2(X20,X21,X28))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(((m1_subset_1(esk4_4(X19,X20,X21,X22),u1_struct_0(X20))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(esk4_4(X19,X20,X21,X22)=esk3_4(X19,X20,X21,X22)|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r1_orders_2(X20,X21,esk4_4(X19,X20,X21,X22))|r2_hidden(esk3_4(X19,X20,X21,X22),u1_struct_0(X22))|~r2_relset_1(u1_struct_0(X22),u1_struct_0(X22),u1_orders_2(X22),k1_toler_1(u1_orders_2(X20),u1_struct_0(X22)))|u1_waybel_0(X19,X22)!=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20),u1_struct_0(X22))|X22=k4_waybel_9(X19,X20,X21)|(~v6_waybel_0(X22,X19)|~l1_waybel_0(X22,X19))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.13/0.36  fof(c_0_9, plain, ![X30, X31, X32]:((v6_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))&(l1_waybel_0(k4_waybel_9(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~l1_waybel_0(X31,X30)|~m1_subset_1(X32,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.13/0.36  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.13/0.36  cnf(c_0_11, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_12, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_13, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((~v2_struct_0(esk6_0)&l1_waybel_0(esk6_0,esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.36  cnf(c_0_15, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_16, plain, (esk2_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4)=X4|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  fof(c_0_21, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.36  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_12]), c_0_13])).
% 0.13/0.36  cnf(c_0_23, negated_conjecture, (esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2)=X2|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,X1,k4_waybel_9(esk5_0,esk6_0,X1),X2),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1)=X1|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.36  fof(c_0_30, plain, ![X16, X17]:(~l1_struct_0(X16)|(~l1_waybel_0(X17,X16)|l1_orders_2(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.13/0.36  fof(c_0_31, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),X1),u1_struct_0(esk6_0))|~r2_hidden(X1,u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,k4_waybel_9(esk5_0,esk6_0,esk7_0),esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)))=esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.36  fof(c_0_34, plain, ![X15]:(~l1_orders_2(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.36  cnf(c_0_35, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.36  fof(c_0_36, plain, ![X18]:((~v2_struct_0(X18)|v1_xboole_0(u1_struct_0(X18))|~l1_struct_0(X18))&(~v1_xboole_0(u1_struct_0(X18))|v2_struct_0(X18)|~l1_struct_0(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).
% 0.13/0.36  cnf(c_0_37, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_33])).
% 0.13/0.36  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (l1_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_18])])).
% 0.13/0.36  cnf(c_0_41, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.36  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_20])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_25]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 47
% 0.13/0.36  # Proof object clause steps            : 30
% 0.13/0.36  # Proof object formula steps           : 17
% 0.13/0.36  # Proof object conjectures             : 21
% 0.13/0.36  # Proof object clause conjectures      : 18
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 16
% 0.13/0.36  # Proof object initial formulas used   : 8
% 0.13/0.36  # Proof object generating inferences   : 12
% 0.13/0.36  # Proof object simplifying inferences  : 21
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 8
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 26
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 26
% 0.13/0.36  # Processed clauses                    : 99
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 9
% 0.13/0.36  # ...remaining for further processing  : 90
% 0.13/0.36  # Other redundant clauses eliminated   : 8
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 2
% 0.13/0.36  # Generated clauses                    : 103
% 0.13/0.36  # ...of the previous two non-trivial   : 88
% 0.13/0.36  # Contextual simplify-reflections      : 12
% 0.13/0.36  # Paramodulations                      : 96
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 8
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 55
% 0.13/0.36  #    Positive orientable unit clauses  : 15
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 3
% 0.13/0.36  #    Non-unit-clauses                  : 37
% 0.13/0.36  # Current number of unprocessed clauses: 40
% 0.13/0.36  # ...number of literals in the above   : 141
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 28
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 2473
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 206
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 21
% 0.13/0.36  # Unit Clause-clause subsumption calls : 62
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 7
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 6654
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.034 s
% 0.13/0.36  # System time              : 0.006 s
% 0.13/0.36  # Total time               : 0.041 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
