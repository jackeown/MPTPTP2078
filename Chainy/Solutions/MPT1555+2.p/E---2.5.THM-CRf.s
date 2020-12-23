%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1555+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 14.26s
% Output     : CNFRefutation 14.26s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 733 expanded)
%              Number of clauses        :   32 ( 259 expanded)
%              Number of leaves         :    5 ( 178 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 (6259 expanded)
%              Number of equality atoms :   29 ( 979 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k2_yellow_0(X1,X3)
            <=> ( r1_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',t25_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k2_yellow_0(X1,X3)
              <=> ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_yellow_0])).

fof(c_0_6,plain,(
    ! [X9452,X9453,X9454,X9455] :
      ( ( r1_lattice3(X9452,X9453,X9454)
        | X9454 != k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( ~ m1_subset_1(X9455,u1_struct_0(X9452))
        | ~ r1_lattice3(X9452,X9453,X9455)
        | r1_orders_2(X9452,X9455,X9454)
        | X9454 != k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( m1_subset_1(esk1068_3(X9452,X9453,X9454),u1_struct_0(X9452))
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( r1_lattice3(X9452,X9453,esk1068_3(X9452,X9453,X9454))
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( ~ r1_orders_2(X9452,esk1068_3(X9452,X9453,X9454),X9454)
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_7,plain,(
    ! [X9495,X9496] :
      ( ~ l1_orders_2(X9495)
      | m1_subset_1(k2_yellow_0(X9495,X9496),u1_struct_0(X9495)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_8,plain,(
    ! [X9539,X9540] :
      ( ( r1_yellow_0(X9539,X9540)
        | v2_struct_0(X9539)
        | ~ v5_orders_2(X9539)
        | ~ v3_lattice3(X9539)
        | ~ l1_orders_2(X9539) )
      & ( r2_yellow_0(X9539,X9540)
        | v2_struct_0(X9539)
        | ~ v5_orders_2(X9539)
        | ~ v3_lattice3(X9539)
        | ~ l1_orders_2(X9539) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X9618] :
      ( ~ v2_struct_0(esk1098_0)
      & v5_orders_2(esk1098_0)
      & v3_lattice3(esk1098_0)
      & l1_orders_2(esk1098_0)
      & m1_subset_1(esk1099_0,u1_struct_0(esk1098_0))
      & ( m1_subset_1(esk1101_0,u1_struct_0(esk1098_0))
        | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
        | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) )
      & ( r1_lattice3(esk1098_0,esk1100_0,esk1101_0)
        | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
        | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) )
      & ( ~ r1_orders_2(esk1098_0,esk1101_0,esk1099_0)
        | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
        | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) )
      & ( r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
        | esk1099_0 = k2_yellow_0(esk1098_0,esk1100_0) )
      & ( ~ m1_subset_1(X9618,u1_struct_0(esk1098_0))
        | ~ r1_lattice3(esk1098_0,esk1100_0,X9618)
        | r1_orders_2(esk1098_0,X9618,esk1099_0)
        | esk1099_0 = k2_yellow_0(esk1098_0,esk1100_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

cnf(c_0_10,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1098_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v3_lattice3(esk1098_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk1098_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1098_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_yellow_0(esk1098_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_19,plain,(
    ! [X6353,X6354,X6355] :
      ( ~ v5_orders_2(X6353)
      | ~ l1_orders_2(X6353)
      | ~ m1_subset_1(X6354,u1_struct_0(X6353))
      | ~ m1_subset_1(X6355,u1_struct_0(X6353))
      | ~ r1_orders_2(X6353,X6354,X6355)
      | ~ r1_orders_2(X6353,X6355,X6354)
      | X6354 = X6355 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk1098_0,X1,esk1099_0)
    | esk1099_0 = k2_yellow_0(esk1098_0,esk1100_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1098_0))
    | ~ r1_lattice3(esk1098_0,esk1100_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk1098_0,X1,k2_yellow_0(esk1098_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk1098_0,X1),u1_struct_0(esk1098_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_13])).

cnf(c_0_23,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
    | esk1099_0 = k2_yellow_0(esk1098_0,esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k2_yellow_0(esk1098_0,esk1100_0) = esk1099_0
    | r1_orders_2(esk1098_0,k2_yellow_0(esk1098_0,esk1100_0),esk1099_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1099_0,u1_struct_0(esk1098_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk1098_0,esk1100_0,esk1099_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk1098_0,esk1100_0,esk1101_0)
    | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
    | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( k2_yellow_0(esk1098_0,esk1100_0) = esk1099_0
    | ~ r1_orders_2(esk1098_0,esk1099_0,k2_yellow_0(esk1098_0,esk1100_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15]),c_0_13]),c_0_22]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1098_0,esk1099_0,k2_yellow_0(esk1098_0,esk1100_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_18]),c_0_13]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_orders_2(esk1098_0,esk1101_0,esk1099_0)
    | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
    | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1101_0,u1_struct_0(esk1098_0))
    | ~ r1_lattice3(esk1098_0,esk1100_0,esk1099_0)
    | esk1099_0 != k2_yellow_0(esk1098_0,esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1098_0,esk1100_0,esk1101_0)
    | k2_yellow_0(esk1098_0,esk1100_0) != esk1099_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( k2_yellow_0(esk1098_0,esk1100_0) = esk1099_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( k2_yellow_0(esk1098_0,esk1100_0) != esk1099_0
    | ~ r1_orders_2(esk1098_0,esk1101_0,esk1099_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1101_0,u1_struct_0(esk1098_0))
    | k2_yellow_0(esk1098_0,esk1100_0) != esk1099_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(esk1098_0,esk1100_0,esk1101_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_orders_2(esk1098_0,esk1101_0,esk1099_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1101_0,u1_struct_0(esk1098_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_36]),c_0_18]),c_0_13])]),c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
