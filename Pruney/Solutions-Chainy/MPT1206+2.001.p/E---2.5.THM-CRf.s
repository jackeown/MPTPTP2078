%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:25 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 308 expanded)
%              Number of clauses        :   38 ( 106 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  316 (1661 expanded)
%              Number of equality atoms :   39 ( 186 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t40_lattices])).

fof(c_0_11,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v13_lattices(esk7_0)
    & l3_lattices(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & k4_lattices(esk7_0,k5_lattices(esk7_0),esk8_0) != k5_lattices(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v6_lattices(X25)
      | ~ l1_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | m1_subset_1(k4_lattices(X25,X26,X27),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_14,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v4_lattices(X39)
      | ~ l2_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | ~ r1_lattices(X39,X40,X41)
      | ~ r1_lattices(X39,X41,X40)
      | X40 = X41 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_22,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_26,plain,(
    ! [X29] :
      ( ( l1_lattices(X29)
        | ~ l3_lattices(X29) )
      & ( l2_lattices(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k4_lattices(esk7_0,X2,esk8_0)
    | ~ r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)
    | ~ r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))
    | ~ l2_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_17])).

cnf(c_0_28,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_29,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v6_lattices(X36)
      | ~ v8_lattices(X36)
      | ~ l3_lattices(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | r1_lattices(X36,k4_lattices(X36,X37,X38),X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_30,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,plain,(
    ! [X6,X7,X8] :
      ( ( k2_lattices(X6,X7,X8) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( k2_lattices(X6,X8,X7) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | X7 = k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( k2_lattices(X6,X7,esk1_2(X6,X7)) != X7
        | k2_lattices(X6,esk1_2(X6,X7),X7) != X7
        | X7 = k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_32,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_lattices(X28)
      | m1_subset_1(k5_lattices(X28),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k4_lattices(esk7_0,X2,esk8_0)
    | ~ r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)
    | ~ r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16])])).

cnf(c_0_34,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_37,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r1_lattices(X10,X11,X12)
        | k1_lattices(X10,X11,X12) = X12
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l2_lattices(X10) )
      & ( k1_lattices(X10,X11,X12) != X12
        | r1_lattices(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l2_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_38,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v8_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | k1_lattices(X20,k2_lattices(X20,X21,X22),X22) = X22
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk5_1(X20),u1_struct_0(X20))
        | v8_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk6_1(X20),u1_struct_0(X20))
        | v8_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( k1_lattices(X20,k2_lattices(X20,esk5_1(X20),esk6_1(X20)),esk6_1(X20)) != esk6_1(X20)
        | v8_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_39,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k4_lattices(esk7_0,X2,esk8_0)
    | ~ r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)
    | ~ r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_36]),c_0_21]),c_0_16])]),c_0_17])).

cnf(c_0_43,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( v13_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk8_0) = X1
    | ~ r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))
    | k1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0)) != k4_lattices(esk7_0,X2,esk8_0)
    | ~ l2_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( k1_lattices(esk7_0,k2_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0)),k4_lattices(esk7_0,X2,esk8_0)) = k4_lattices(esk7_0,X2,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_36]),c_0_16])]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( k2_lattices(esk7_0,k5_lattices(esk7_0),k4_lattices(esk7_0,X1,esk8_0)) = k5_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_46])]),c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_16]),c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk8_0) = X1
    | k1_lattices(esk7_0,X1,k4_lattices(esk7_0,X1,esk8_0)) != k4_lattices(esk7_0,X1,esk8_0)
    | ~ l2_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_lattices(esk7_0,k5_lattices(esk7_0),k4_lattices(esk7_0,X1,esk8_0)) = k4_lattices(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( k4_lattices(esk7_0,k5_lattices(esk7_0),esk8_0) != k5_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( ~ l2_lattices(esk7_0)
    | ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_52])]),c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( ~ l2_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_34]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:21:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.36/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.36/0.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.36/0.53  #
% 0.36/0.53  # Preprocessing time       : 0.044 s
% 0.36/0.53  # Presaturation interreduction done
% 0.36/0.53  
% 0.36/0.53  # Proof found!
% 0.36/0.53  # SZS status Theorem
% 0.36/0.53  # SZS output start CNFRefutation
% 0.36/0.53  fof(t40_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 0.36/0.53  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.36/0.53  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 0.36/0.53  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 0.36/0.53  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.36/0.53  fof(t23_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 0.36/0.53  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.36/0.53  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.36/0.53  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.36/0.53  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.36/0.53  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)))), inference(assume_negation,[status(cth)],[t40_lattices])).
% 0.36/0.53  fof(c_0_11, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.36/0.53  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v13_lattices(esk7_0))&l3_lattices(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&k4_lattices(esk7_0,k5_lattices(esk7_0),esk8_0)!=k5_lattices(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.36/0.53  fof(c_0_13, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v6_lattices(X25)|~l1_lattices(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|m1_subset_1(k4_lattices(X25,X26,X27),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 0.36/0.53  cnf(c_0_14, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.53  cnf(c_0_15, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  cnf(c_0_16, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  fof(c_0_18, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v4_lattices(X39)|~l2_lattices(X39)|(~m1_subset_1(X40,u1_struct_0(X39))|(~m1_subset_1(X41,u1_struct_0(X39))|(~r1_lattices(X39,X40,X41)|~r1_lattices(X39,X41,X40)|X40=X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.36/0.53  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.53  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  cnf(c_0_21, negated_conjecture, (v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])]), c_0_17])).
% 0.36/0.53  cnf(c_0_22, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.53  cnf(c_0_23, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.36/0.53  cnf(c_0_24, negated_conjecture, (m1_subset_1(k4_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), c_0_17])).
% 0.36/0.53  cnf(c_0_25, negated_conjecture, (v4_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_16])]), c_0_17])).
% 0.36/0.53  fof(c_0_26, plain, ![X29]:((l1_lattices(X29)|~l3_lattices(X29))&(l2_lattices(X29)|~l3_lattices(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.36/0.53  cnf(c_0_27, negated_conjecture, (X1=k4_lattices(esk7_0,X2,esk8_0)|~r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)|~r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))|~l2_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_17])).
% 0.36/0.53  cnf(c_0_28, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.36/0.53  fof(c_0_29, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v6_lattices(X36)|~v8_lattices(X36)|~l3_lattices(X36)|(~m1_subset_1(X37,u1_struct_0(X36))|(~m1_subset_1(X38,u1_struct_0(X36))|r1_lattices(X36,k4_lattices(X36,X37,X38),X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).
% 0.36/0.53  cnf(c_0_30, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.53  fof(c_0_31, plain, ![X6, X7, X8]:(((k2_lattices(X6,X7,X8)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6)))&(k2_lattices(X6,X8,X7)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6))))&((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|X7=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6)))&(k2_lattices(X6,X7,esk1_2(X6,X7))!=X7|k2_lattices(X6,esk1_2(X6,X7),X7)!=X7|X7=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.36/0.53  fof(c_0_32, plain, ![X28]:(v2_struct_0(X28)|~l1_lattices(X28)|m1_subset_1(k5_lattices(X28),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.36/0.53  cnf(c_0_33, negated_conjecture, (X1=k4_lattices(esk7_0,X2,esk8_0)|~r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)|~r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_16])])).
% 0.36/0.53  cnf(c_0_34, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.36/0.53  cnf(c_0_35, plain, (v2_struct_0(X1)|r1_lattices(X1,k4_lattices(X1,X2,X3),X2)|~v6_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.36/0.53  cnf(c_0_36, negated_conjecture, (v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_15]), c_0_16])]), c_0_17])).
% 0.36/0.53  fof(c_0_37, plain, ![X10, X11, X12]:((~r1_lattices(X10,X11,X12)|k1_lattices(X10,X11,X12)=X12|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l2_lattices(X10)))&(k1_lattices(X10,X11,X12)!=X12|r1_lattices(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l2_lattices(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.36/0.53  fof(c_0_38, plain, ![X20, X21, X22]:((~v8_lattices(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|(~m1_subset_1(X22,u1_struct_0(X20))|k1_lattices(X20,k2_lattices(X20,X21,X22),X22)=X22))|(v2_struct_0(X20)|~l3_lattices(X20)))&((m1_subset_1(esk5_1(X20),u1_struct_0(X20))|v8_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))&((m1_subset_1(esk6_1(X20),u1_struct_0(X20))|v8_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))&(k1_lattices(X20,k2_lattices(X20,esk5_1(X20),esk6_1(X20)),esk6_1(X20))!=esk6_1(X20)|v8_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.36/0.53  cnf(c_0_39, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|X2!=k5_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.36/0.53  cnf(c_0_40, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.36/0.53  cnf(c_0_41, negated_conjecture, (X1=k4_lattices(esk7_0,X2,esk8_0)|~r1_lattices(esk7_0,k4_lattices(esk7_0,X2,esk8_0),X1)|~r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_16])])).
% 0.36/0.53  cnf(c_0_42, negated_conjecture, (r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_36]), c_0_21]), c_0_16])]), c_0_17])).
% 0.36/0.53  cnf(c_0_43, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.36/0.53  cnf(c_0_44, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.36/0.53  cnf(c_0_45, plain, (k2_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_40])).
% 0.36/0.53  cnf(c_0_46, negated_conjecture, (v13_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  cnf(c_0_47, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.36/0.53  cnf(c_0_48, negated_conjecture, (k4_lattices(esk7_0,X1,esk8_0)=X1|~r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.36/0.53  cnf(c_0_49, negated_conjecture, (r1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))|k1_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0))!=k4_lattices(esk7_0,X2,esk8_0)|~l2_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_24]), c_0_17])).
% 0.36/0.53  cnf(c_0_50, negated_conjecture, (k1_lattices(esk7_0,k2_lattices(esk7_0,X1,k4_lattices(esk7_0,X2,esk8_0)),k4_lattices(esk7_0,X2,esk8_0))=k4_lattices(esk7_0,X2,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_36]), c_0_16])]), c_0_17])).
% 0.36/0.53  cnf(c_0_51, negated_conjecture, (k2_lattices(esk7_0,k5_lattices(esk7_0),k4_lattices(esk7_0,X1,esk8_0))=k5_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_46])]), c_0_17])).
% 0.36/0.53  cnf(c_0_52, negated_conjecture, (m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_16]), c_0_17])).
% 0.36/0.53  cnf(c_0_53, negated_conjecture, (k4_lattices(esk7_0,X1,esk8_0)=X1|k1_lattices(esk7_0,X1,k4_lattices(esk7_0,X1,esk8_0))!=k4_lattices(esk7_0,X1,esk8_0)|~l2_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.36/0.53  cnf(c_0_54, negated_conjecture, (k1_lattices(esk7_0,k5_lattices(esk7_0),k4_lattices(esk7_0,X1,esk8_0))=k4_lattices(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.36/0.53  cnf(c_0_55, negated_conjecture, (k4_lattices(esk7_0,k5_lattices(esk7_0),esk8_0)!=k5_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.53  cnf(c_0_56, negated_conjecture, (~l2_lattices(esk7_0)|~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_52])]), c_0_55])).
% 0.36/0.53  cnf(c_0_57, negated_conjecture, (~l2_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_34]), c_0_16])])).
% 0.36/0.53  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_16])]), ['proof']).
% 0.36/0.53  # SZS output end CNFRefutation
% 0.36/0.53  # Proof object total steps             : 59
% 0.36/0.53  # Proof object clause steps            : 38
% 0.36/0.53  # Proof object formula steps           : 21
% 0.36/0.53  # Proof object conjectures             : 27
% 0.36/0.53  # Proof object clause conjectures      : 24
% 0.36/0.53  # Proof object formula conjectures     : 3
% 0.36/0.53  # Proof object initial clauses used    : 18
% 0.36/0.53  # Proof object initial formulas used   : 10
% 0.36/0.53  # Proof object generating inferences   : 19
% 0.36/0.53  # Proof object simplifying inferences  : 44
% 0.36/0.53  # Training examples: 0 positive, 0 negative
% 0.36/0.53  # Parsed axioms                        : 13
% 0.36/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.53  # Initial clauses                      : 37
% 0.36/0.53  # Removed in clause preprocessing      : 1
% 0.36/0.53  # Initial clauses in saturation        : 36
% 0.36/0.53  # Processed clauses                    : 735
% 0.36/0.53  # ...of these trivial                  : 0
% 0.36/0.53  # ...subsumed                          : 130
% 0.36/0.53  # ...remaining for further processing  : 605
% 0.36/0.53  # Other redundant clauses eliminated   : 2
% 0.36/0.53  # Clauses deleted for lack of memory   : 0
% 0.36/0.53  # Backward-subsumed                    : 109
% 0.36/0.53  # Backward-rewritten                   : 0
% 0.36/0.53  # Generated clauses                    : 5961
% 0.36/0.53  # ...of the previous two non-trivial   : 5943
% 0.36/0.53  # Contextual simplify-reflections      : 21
% 0.36/0.53  # Paramodulations                      : 5959
% 0.36/0.53  # Factorizations                       : 0
% 0.36/0.53  # Equation resolutions                 : 2
% 0.36/0.53  # Propositional unsat checks           : 0
% 0.36/0.53  #    Propositional check models        : 0
% 0.36/0.53  #    Propositional check unsatisfiable : 0
% 0.36/0.53  #    Propositional clauses             : 0
% 0.36/0.53  #    Propositional clauses after purity: 0
% 0.36/0.53  #    Propositional unsat core size     : 0
% 0.36/0.53  #    Propositional preprocessing time  : 0.000
% 0.36/0.53  #    Propositional encoding time       : 0.000
% 0.36/0.53  #    Propositional solver time         : 0.000
% 0.36/0.53  #    Success case prop preproc time    : 0.000
% 0.36/0.53  #    Success case prop encoding time   : 0.000
% 0.36/0.53  #    Success case prop solver time     : 0.000
% 0.36/0.53  # Current number of processed clauses  : 458
% 0.36/0.53  #    Positive orientable unit clauses  : 15
% 0.36/0.53  #    Positive unorientable unit clauses: 0
% 0.36/0.53  #    Negative unit clauses             : 3
% 0.36/0.53  #    Non-unit-clauses                  : 440
% 0.36/0.53  # Current number of unprocessed clauses: 5278
% 0.36/0.53  # ...number of literals in the above   : 14604
% 0.36/0.53  # Current number of archived formulas  : 0
% 0.36/0.53  # Current number of archived clauses   : 145
% 0.36/0.53  # Clause-clause subsumption calls (NU) : 102271
% 0.36/0.53  # Rec. Clause-clause subsumption calls : 43065
% 0.36/0.53  # Non-unit clause-clause subsumptions  : 260
% 0.36/0.53  # Unit Clause-clause subsumption calls : 649
% 0.36/0.53  # Rewrite failures with RHS unbound    : 0
% 0.36/0.53  # BW rewrite match attempts            : 6
% 0.36/0.53  # BW rewrite match successes           : 0
% 0.36/0.53  # Condensation attempts                : 0
% 0.36/0.53  # Condensation successes               : 0
% 0.36/0.53  # Termbank termtop insertions          : 229322
% 0.36/0.53  
% 0.36/0.53  # -------------------------------------------------
% 0.36/0.53  # User time                : 0.199 s
% 0.36/0.53  # System time              : 0.009 s
% 0.36/0.53  # Total time               : 0.208 s
% 0.36/0.53  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
