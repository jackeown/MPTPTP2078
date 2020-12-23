%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1566+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 16.62s
% Output     : CNFRefutation 16.62s
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
fof(t44_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t44_yellow_0])).

fof(c_0_7,plain,(
    ! [X9457] :
      ( ~ l1_orders_2(X9457)
      | k3_yellow_0(X9457) = k1_yellow_0(X9457,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1099_0)
    & v5_orders_2(esk1099_0)
    & v1_yellow_0(esk1099_0)
    & l1_orders_2(esk1099_0)
    & m1_subset_1(esk1100_0,u1_struct_0(esk1099_0))
    & ~ r1_orders_2(esk1099_0,k3_yellow_0(esk1099_0),esk1100_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X9488,X9489,X9490,X9491] :
      ( ( r2_lattice3(X9488,X9489,X9490)
        | X9490 != k1_yellow_0(X9488,X9489)
        | ~ r1_yellow_0(X9488,X9489)
        | ~ m1_subset_1(X9490,u1_struct_0(X9488))
        | ~ l1_orders_2(X9488) )
      & ( ~ m1_subset_1(X9491,u1_struct_0(X9488))
        | ~ r2_lattice3(X9488,X9489,X9491)
        | r1_orders_2(X9488,X9490,X9491)
        | X9490 != k1_yellow_0(X9488,X9489)
        | ~ r1_yellow_0(X9488,X9489)
        | ~ m1_subset_1(X9490,u1_struct_0(X9488))
        | ~ l1_orders_2(X9488) )
      & ( m1_subset_1(esk1079_3(X9488,X9489,X9490),u1_struct_0(X9488))
        | ~ r2_lattice3(X9488,X9489,X9490)
        | X9490 = k1_yellow_0(X9488,X9489)
        | ~ r1_yellow_0(X9488,X9489)
        | ~ m1_subset_1(X9490,u1_struct_0(X9488))
        | ~ l1_orders_2(X9488) )
      & ( r2_lattice3(X9488,X9489,esk1079_3(X9488,X9489,X9490))
        | ~ r2_lattice3(X9488,X9489,X9490)
        | X9490 = k1_yellow_0(X9488,X9489)
        | ~ r1_yellow_0(X9488,X9489)
        | ~ m1_subset_1(X9490,u1_struct_0(X9488))
        | ~ l1_orders_2(X9488) )
      & ( ~ r1_orders_2(X9488,X9490,esk1079_3(X9488,X9489,X9490))
        | ~ r2_lattice3(X9488,X9489,X9490)
        | X9490 = k1_yellow_0(X9488,X9489)
        | ~ r1_yellow_0(X9488,X9489)
        | ~ m1_subset_1(X9490,u1_struct_0(X9488))
        | ~ l1_orders_2(X9488) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_10,plain,(
    ! [X9494,X9495] :
      ( ~ l1_orders_2(X9494)
      | m1_subset_1(k1_yellow_0(X9494,X9495),u1_struct_0(X9494)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_11,plain,(
    ! [X9657,X9658] :
      ( ( r2_lattice3(X9657,k1_xboole_0,X9658)
        | ~ m1_subset_1(X9658,u1_struct_0(X9657))
        | ~ l1_orders_2(X9657) )
      & ( r1_lattice3(X9657,k1_xboole_0,X9658)
        | ~ m1_subset_1(X9658,u1_struct_0(X9657))
        | ~ l1_orders_2(X9657) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_12,plain,(
    ! [X9646] :
      ( ( r1_yellow_0(X9646,k1_xboole_0)
        | v2_struct_0(X9646)
        | ~ v5_orders_2(X9646)
        | ~ v1_yellow_0(X9646)
        | ~ l1_orders_2(X9646) )
      & ( r2_yellow_0(X9646,u1_struct_0(X9646))
        | v2_struct_0(X9646)
        | ~ v5_orders_2(X9646)
        | ~ v1_yellow_0(X9646)
        | ~ l1_orders_2(X9646) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_13,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1100_0,u1_struct_0(esk1099_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_yellow_0(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_orders_2(esk1099_0,k3_yellow_0(esk1099_0),esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k3_yellow_0(esk1099_0) = k1_yellow_0(esk1099_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk1099_0,k1_xboole_0,esk1100_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( r1_yellow_0(esk1099_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_orders_2(esk1099_0,k1_yellow_0(esk1099_0,k1_xboole_0),esk1100_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_14]),c_0_18])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
