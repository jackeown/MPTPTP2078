%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1533+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :   15 (  33 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   61 ( 187 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_yellow_0,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r2_lattice3(X1,X2,X3)
                  & r1_orders_2(X1,X3,X4) )
               => r2_lattice3(X1,X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow_0)).

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( ( r2_lattice3(X1,X2,X3)
                    & r1_orders_2(X1,X3,X4) )
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_yellow_0])).

fof(c_0_3,plain,(
    ! [X9468,X9469,X9470,X9471] :
      ( ( ~ r1_lattice3(X9468,X9471,X9470)
        | r1_lattice3(X9468,X9471,X9469)
        | ~ r1_orders_2(X9468,X9469,X9470)
        | ~ m1_subset_1(X9470,u1_struct_0(X9468))
        | ~ m1_subset_1(X9469,u1_struct_0(X9468))
        | ~ v4_orders_2(X9468)
        | ~ l1_orders_2(X9468) )
      & ( ~ r2_lattice3(X9468,X9471,X9469)
        | r2_lattice3(X9468,X9471,X9470)
        | ~ r1_orders_2(X9468,X9469,X9470)
        | ~ m1_subset_1(X9470,u1_struct_0(X9468))
        | ~ m1_subset_1(X9469,u1_struct_0(X9468))
        | ~ v4_orders_2(X9468)
        | ~ l1_orders_2(X9468) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

fof(c_0_4,negated_conjecture,
    ( v4_orders_2(esk1068_0)
    & l1_orders_2(esk1068_0)
    & m1_subset_1(esk1070_0,u1_struct_0(esk1068_0))
    & m1_subset_1(esk1071_0,u1_struct_0(esk1068_0))
    & r2_lattice3(esk1068_0,esk1069_0,esk1070_0)
    & r1_orders_2(esk1068_0,esk1070_0,esk1071_0)
    & ~ r2_lattice3(esk1068_0,esk1069_0,esk1071_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_orders_2(esk1068_0,esk1070_0,esk1071_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v4_orders_2(esk1068_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1068_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk1071_0,u1_struct_0(esk1068_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk1070_0,u1_struct_0(esk1068_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r2_lattice3(esk1068_0,X1,esk1071_0)
    | ~ r2_lattice3(esk1068_0,X1,esk1070_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_12,negated_conjecture,
    ( r2_lattice3(esk1068_0,esk1069_0,esk1070_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_lattice3(esk1068_0,esk1069_0,esk1071_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
