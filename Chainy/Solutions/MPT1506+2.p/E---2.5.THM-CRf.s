%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1506+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 13.19s
% Output     : CNFRefutation 13.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  36 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :  104 ( 230 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(t40_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
             => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(c_0_3,plain,(
    ! [X9259,X9260,X9261,X9262,X9263] :
      ( ( r3_lattice3(X9259,X9260,X9261)
        | X9260 != k16_lattice3(X9259,X9261)
        | ~ m1_subset_1(X9260,u1_struct_0(X9259))
        | v2_struct_0(X9259)
        | ~ v10_lattices(X9259)
        | ~ v4_lattice3(X9259)
        | ~ l3_lattices(X9259) )
      & ( ~ m1_subset_1(X9262,u1_struct_0(X9259))
        | ~ r3_lattice3(X9259,X9262,X9261)
        | r3_lattices(X9259,X9262,X9260)
        | X9260 != k16_lattice3(X9259,X9261)
        | ~ m1_subset_1(X9260,u1_struct_0(X9259))
        | v2_struct_0(X9259)
        | ~ v10_lattices(X9259)
        | ~ v4_lattice3(X9259)
        | ~ l3_lattices(X9259) )
      & ( m1_subset_1(esk1040_3(X9259,X9260,X9263),u1_struct_0(X9259))
        | ~ r3_lattice3(X9259,X9260,X9263)
        | X9260 = k16_lattice3(X9259,X9263)
        | ~ m1_subset_1(X9260,u1_struct_0(X9259))
        | v2_struct_0(X9259)
        | ~ v10_lattices(X9259)
        | ~ v4_lattice3(X9259)
        | ~ l3_lattices(X9259) )
      & ( r3_lattice3(X9259,esk1040_3(X9259,X9260,X9263),X9263)
        | ~ r3_lattice3(X9259,X9260,X9263)
        | X9260 = k16_lattice3(X9259,X9263)
        | ~ m1_subset_1(X9260,u1_struct_0(X9259))
        | v2_struct_0(X9259)
        | ~ v10_lattices(X9259)
        | ~ v4_lattice3(X9259)
        | ~ l3_lattices(X9259) )
      & ( ~ r3_lattices(X9259,esk1040_3(X9259,X9260,X9263),X9260)
        | ~ r3_lattice3(X9259,X9260,X9263)
        | X9260 = k16_lattice3(X9259,X9263)
        | ~ m1_subset_1(X9260,u1_struct_0(X9259))
        | v2_struct_0(X9259)
        | ~ v10_lattices(X9259)
        | ~ v4_lattice3(X9259)
        | ~ l3_lattices(X9259) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_4,plain,(
    ! [X8973,X8974] :
      ( v2_struct_0(X8973)
      | ~ l3_lattices(X8973)
      | m1_subset_1(k16_lattice3(X8973,X8974),u1_struct_0(X8973)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r3_lattice3(X1,X2,X3)
               => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_lattice3])).

cnf(c_0_6,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0)
    & v10_lattices(esk1043_0)
    & v4_lattice3(esk1043_0)
    & l3_lattices(esk1043_0)
    & m1_subset_1(esk1044_0,u1_struct_0(esk1043_0))
    & r3_lattice3(esk1043_0,esk1044_0,esk1045_0)
    & ~ r3_lattices(esk1043_0,esk1044_0,k16_lattice3(esk1043_0,esk1045_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_6]),c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r3_lattice3(esk1043_0,esk1044_0,esk1045_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v4_lattice3(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk1044_0,u1_struct_0(esk1043_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ r3_lattices(esk1043_0,esk1044_0,k16_lattice3(esk1043_0,esk1045_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
