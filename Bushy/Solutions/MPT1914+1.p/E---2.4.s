%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t12_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 128 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',dt_u1_orders_2)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',dt_k7_lattice3)).

fof(t12_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',t12_yellow_6)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',abstractness_v1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',d5_lattice3)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t12_yellow_6.p',redefinition_k3_relset_1)).

fof(c_0_7,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | m1_subset_1(u1_orders_2(X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X18)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_8,plain,(
    ! [X16] :
      ( ( v1_orders_2(k7_lattice3(X16))
        | ~ l1_orders_2(X16) )
      & ( l1_orders_2(k7_lattice3(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1)) ) ),
    inference(assume_negation,[status(cth)],[t12_yellow_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & u1_struct_0(esk1_0) != u1_struct_0(k7_lattice3(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X23 = X25
        | g1_orders_2(X23,X24) != g1_orders_2(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) )
      & ( X24 = X26
        | g1_orders_2(X23,X24) != g1_orders_2(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(X1)),u1_struct_0(k7_lattice3(X1)))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(u1_orders_2(k7_lattice3(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)),u1_struct_0(k7_lattice3(esk1_0))))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_orders_2(X6)
      | X6 = g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_19,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = X1
    | g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2)
    | ~ v1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k7_lattice3(X9) = g1_orders_2(u1_struct_0(X9),k3_relset_1(u1_struct_0(X9),u1_struct_0(X9),u1_orders_2(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k3_relset_1(X31,X32,X33) = k4_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_26,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_11]),c_0_15])])).

cnf(c_0_29,plain,
    ( g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = u1_struct_0(X1)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk1_0) != u1_struct_0(k7_lattice3(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_15])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
