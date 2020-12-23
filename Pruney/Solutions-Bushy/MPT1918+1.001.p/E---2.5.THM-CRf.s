%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  99 expanded)
%              Number of clauses        :   21 (  39 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 369 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t16_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_0(X3,X2)
             => m1_yellow_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

fof(c_0_4,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(u1_struct_0(X5),u1_struct_0(X4))
        | ~ m1_yellow_0(X5,X4)
        | ~ l1_orders_2(X5)
        | ~ l1_orders_2(X4) )
      & ( r1_tarski(u1_orders_2(X5),u1_orders_2(X4))
        | ~ m1_yellow_0(X5,X4)
        | ~ l1_orders_2(X5)
        | ~ l1_orders_2(X4) )
      & ( ~ r1_tarski(u1_struct_0(X5),u1_struct_0(X4))
        | ~ r1_tarski(u1_orders_2(X5),u1_orders_2(X4))
        | m1_yellow_0(X5,X4)
        | ~ l1_orders_2(X5)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_5,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(X6)
      | ~ m1_yellow_0(X7,X6)
      | l1_orders_2(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_7,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_yellow_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_0(X3,X2)
               => m1_yellow_0(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow_6])).

cnf(c_0_13,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,u1_orders_2(X2))
    | ~ r1_tarski(X1,u1_orders_2(X3))
    | ~ m1_yellow_0(X3,X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & ~ m1_yellow_0(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X3,X2)
    | ~ m1_yellow_0(X1,X3)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X3,X2)
    | ~ m1_yellow_0(X1,X3)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_8])).

cnf(c_0_21,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))
    | ~ m1_yellow_0(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_yellow_0(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_18]),c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( m1_yellow_0(X1,esk1_0)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_24]),c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_yellow_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
