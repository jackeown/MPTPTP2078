%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1567+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 15.48s
% Output     : CNFRefutation 15.48s
% Verified   : 
% Statistics : Number of formulae       :   30 (  61 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  125 ( 291 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t43_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_yellow_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_0])).

fof(c_0_7,plain,(
    ! [X9458] :
      ( ~ l1_orders_2(X9458)
      | k4_yellow_0(X9458) = k2_yellow_0(X9458,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1099_0)
    & v5_orders_2(esk1099_0)
    & v2_yellow_0(esk1099_0)
    & l1_orders_2(esk1099_0)
    & m1_subset_1(esk1100_0,u1_struct_0(esk1099_0))
    & ~ r1_orders_2(esk1099_0,esk1100_0,k4_yellow_0(esk1099_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X9497,X9498] :
      ( ~ l1_orders_2(X9497)
      | m1_subset_1(k2_yellow_0(X9497,X9498),u1_struct_0(X9497)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_11,plain,(
    ! [X9661,X9662] :
      ( ( r2_lattice3(X9661,k1_xboole_0,X9662)
        | ~ m1_subset_1(X9662,u1_struct_0(X9661))
        | ~ l1_orders_2(X9661) )
      & ( r1_lattice3(X9661,k1_xboole_0,X9662)
        | ~ m1_subset_1(X9662,u1_struct_0(X9661))
        | ~ l1_orders_2(X9661) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_12,plain,(
    ! [X9649] :
      ( ( r2_yellow_0(X9649,k1_xboole_0)
        | v2_struct_0(X9649)
        | ~ v5_orders_2(X9649)
        | ~ v2_yellow_0(X9649)
        | ~ l1_orders_2(X9649) )
      & ( r1_yellow_0(X9649,u1_struct_0(X9649))
        | v2_struct_0(X9649)
        | ~ v5_orders_2(X9649)
        | ~ v2_yellow_0(X9649)
        | ~ l1_orders_2(X9649) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_yellow_0])])])])).

cnf(c_0_13,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1100_0,u1_struct_0(esk1099_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v2_yellow_0(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_orders_2(esk1099_0,esk1100_0,k4_yellow_0(esk1099_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k4_yellow_0(esk1099_0) = k2_yellow_0(esk1099_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattice3(esk1099_0,k1_xboole_0,esk1100_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( r2_yellow_0(esk1099_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_orders_2(esk1099_0,esk1100_0,k2_yellow_0(esk1099_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_14]),c_0_18])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
