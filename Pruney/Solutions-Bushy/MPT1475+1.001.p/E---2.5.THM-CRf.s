%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1475+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:17 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 485 expanded)
%              Number of clauses        :   33 ( 209 expanded)
%              Number of leaves         :    7 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 (1058 expanded)
%              Number of equality atoms :   43 ( 312 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_lattice3,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(involutiveness_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,k3_relset_1(X1,X2,X3)) = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t8_lattice3])).

fof(c_0_8,plain,(
    ! [X7] :
      ( ( v1_orders_2(k7_lattice3(X7))
        | ~ l1_orders_2(X7) )
      & ( l1_orders_2(k7_lattice3(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_11,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_14,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

fof(c_0_20,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | k7_lattice3(X6) = g1_orders_2(u1_struct_0(X6),k3_relset_1(u1_struct_0(X6),u1_struct_0(X6),u1_orders_2(X6))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(u1_orders_2(k7_lattice3(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)),u1_struct_0(k7_lattice3(esk1_0))))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])])).

cnf(c_0_24,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))),u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))),u1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_26]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),k3_relset_1(u1_struct_0(k7_lattice3(esk1_0)),u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))) = X1
    | k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32]),c_0_32])).

fof(c_0_36,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k3_relset_1(X13,X14,k3_relset_1(X13,X14,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) = X1
    | k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k3_relset_1(X2,X3,k3_relset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = u1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0))) = u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).

%------------------------------------------------------------------------------
