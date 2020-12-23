%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1178+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   35 (  79 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 407 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(t78_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_orders_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X8,X7)
        | m2_orders_2(X8,X5,X6)
        | X7 != k4_orders_2(X5,X6)
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m2_orders_2(X9,X5,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_orders_2(X5,X6)
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X10),X10)
        | ~ m2_orders_2(esk1_3(X5,X6,X10),X5,X6)
        | X10 = k4_orders_2(X5,X6)
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X10),X10)
        | m2_orders_2(esk1_3(X5,X6,X10),X5,X6)
        | X10 = k4_orders_2(X5,X6)
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))
    & k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ( X17 = k1_xboole_0
        | ~ r2_hidden(X17,X16)
        | k3_tarski(X16) != k1_xboole_0 )
      & ( esk2_1(X18) != k1_xboole_0
        | k3_tarski(X18) = k1_xboole_0 )
      & ( r2_hidden(esk2_1(X18),X18)
        | k3_tarski(X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k4_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
      | m2_orders_2(k1_tarski(k1_funct_1(X15,u1_struct_0(X14))),X14,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X13] :
      ( ~ v1_xboole_0(X13)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk3_0,esk4_0))
    | ~ m2_orders_2(X1,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_27,plain,(
    ! [X12] : ~ v1_xboole_0(k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m2_orders_2(X1,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( m2_orders_2(k1_tarski(k1_funct_1(esk4_0,u1_struct_0(esk3_0))),esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk4_0,u1_struct_0(esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),
    [proof]).

%------------------------------------------------------------------------------
