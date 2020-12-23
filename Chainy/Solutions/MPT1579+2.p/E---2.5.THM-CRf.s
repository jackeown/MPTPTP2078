%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1579+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :   17 (  46 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    2 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 ( 234 expanded)
%              Number of equality atoms :   15 (  68 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( ( v4_yellow_0(X3,X1)
                & m1_yellow_0(X3,X1) )
             => ( u1_struct_0(X2) = u1_struct_0(X3)
               => g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_yellow_0)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( ( v4_yellow_0(X3,X1)
                  & m1_yellow_0(X3,X1) )
               => ( u1_struct_0(X2) = u1_struct_0(X3)
                 => g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_yellow_0])).

fof(c_0_3,plain,(
    ! [X9461,X9462] :
      ( ( ~ v4_yellow_0(X9462,X9461)
        | u1_orders_2(X9462) = k1_toler_1(u1_orders_2(X9461),u1_struct_0(X9462))
        | ~ m1_yellow_0(X9462,X9461)
        | ~ l1_orders_2(X9461) )
      & ( u1_orders_2(X9462) != k1_toler_1(u1_orders_2(X9461),u1_struct_0(X9462))
        | v4_yellow_0(X9462,X9461)
        | ~ m1_yellow_0(X9462,X9461)
        | ~ l1_orders_2(X9461) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

fof(c_0_4,negated_conjecture,
    ( l1_orders_2(esk1112_0)
    & v4_yellow_0(esk1113_0,esk1112_0)
    & m1_yellow_0(esk1113_0,esk1112_0)
    & v4_yellow_0(esk1114_0,esk1112_0)
    & m1_yellow_0(esk1114_0,esk1112_0)
    & u1_struct_0(esk1113_0) = u1_struct_0(esk1114_0)
    & g1_orders_2(u1_struct_0(esk1113_0),u1_orders_2(esk1113_0)) != g1_orders_2(u1_struct_0(esk1114_0),u1_orders_2(esk1114_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_yellow_0(esk1114_0,esk1112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v4_yellow_0(esk1114_0,esk1112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1113_0),u1_orders_2(esk1113_0)) != g1_orders_2(u1_struct_0(esk1114_0),u1_orders_2(esk1114_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( u1_struct_0(esk1113_0) = u1_struct_0(esk1114_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( m1_yellow_0(esk1113_0,esk1112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( v4_yellow_0(esk1113_0,esk1112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk1112_0),u1_struct_0(esk1114_0)) = u1_orders_2(esk1114_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])])).

cnf(c_0_14,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1114_0),u1_orders_2(esk1113_0)) != g1_orders_2(u1_struct_0(esk1114_0),u1_orders_2(esk1114_0)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk1113_0) = u1_orders_2(esk1114_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_11]),c_0_10]),c_0_12]),c_0_8])]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
