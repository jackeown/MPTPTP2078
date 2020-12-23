%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1476+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 22.22s
% Output     : CNFRefutation 22.22s
% Verified   : 
% Statistics : Number of formulae       :  122 (30696 expanded)
%              Number of clauses        :   93 (13193 expanded)
%              Number of leaves         :   14 (7580 expanded)
%              Depth                    :   34
%              Number of atoms          :  329 (97282 expanded)
%              Number of equality atoms :   89 (17619 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(t9_lattice3,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r1_orders_2(k7_lattice3(X1),k8_lattice3(X1,X3),k8_lattice3(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_lattice3)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(dt_k8_lattice3,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_lattice3)).

fof(d6_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k8_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

fof(involutiveness_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,k3_relset_1(X1,X2,X3)) = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_14,plain,(
    ! [X31] :
      ( ~ l1_orders_2(X31)
      | m1_subset_1(u1_orders_2(X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X31)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_15,plain,(
    ! [X28] :
      ( ( v1_orders_2(k7_lattice3(X28))
        | ~ l1_orders_2(X28) )
      & ( l1_orders_2(k7_lattice3(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_orders_2(X1,X2,X3)
                <=> r1_orders_2(k7_lattice3(X1),k8_lattice3(X1,X3),k8_lattice3(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_lattice3])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0)
      | ~ r1_orders_2(k7_lattice3(esk3_0),k8_lattice3(esk3_0,esk5_0),k8_lattice3(esk3_0,esk4_0)) )
    & ( r1_orders_2(esk3_0,esk4_0,esk5_0)
      | r1_orders_2(k7_lattice3(esk3_0),k8_lattice3(esk3_0,esk5_0),k8_lattice3(esk3_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X32,X33,X34,X35] :
      ( ( X32 = X34
        | g1_orders_2(X32,X33) != g1_orders_2(X34,X35)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X32))) )
      & ( X33 = X35
        | g1_orders_2(X32,X33) != g1_orders_2(X34,X35)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(X1)),u1_struct_0(k7_lattice3(X1)))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(u1_orders_2(k7_lattice3(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(esk3_0)),u1_struct_0(k7_lattice3(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = X1
    | g1_orders_2(u1_struct_0(k7_lattice3(esk3_0)),u1_orders_2(k7_lattice3(esk3_0))) != g1_orders_2(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X1,X2)
    | ~ v1_orders_2(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k7_lattice3(X9) = g1_orders_2(u1_struct_0(X9),k3_relset_1(u1_struct_0(X9),u1_struct_0(X9),u1_orders_2(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

fof(c_0_31,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k3_relset_1(X40,X41,X42) = k4_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X1,X2)
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])])).

cnf(c_0_33,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_22])])).

cnf(c_0_36,plain,
    ( g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = u1_struct_0(X1)
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_22])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(u1_orders_2(k7_lattice3(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_38]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = X1
    | g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(k7_lattice3(esk3_0))) != g1_orders_2(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(k7_lattice3(esk3_0))) = k7_lattice3(esk3_0)
    | ~ v1_orders_2(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X2,X1)
    | ~ v1_orders_2(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X2,X1)
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_22])])).

cnf(c_0_45,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_18]),c_0_22])])).

cnf(c_0_46,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = k4_relat_1(u1_orders_2(X1))
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k4_relat_1(u1_orders_2(X1)) = X2
    | k7_lattice3(esk3_0) != g1_orders_2(X3,X2)
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_48,plain,(
    ! [X29,X30] :
      ( ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | m1_subset_1(k8_lattice3(X29,X30),u1_struct_0(k7_lattice3(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_lattice3])])).

cnf(c_0_49,negated_conjecture,
    ( k4_relat_1(u1_orders_2(esk3_0)) = X1
    | k7_lattice3(esk3_0) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(k7_lattice3(esk3_0))) = k7_lattice3(X1)
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_46])).

cnf(c_0_51,plain,
    ( m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_53,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | k8_lattice3(X10,X11) = X11 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_lattice3])])])).

cnf(c_0_54,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = k4_relat_1(u1_orders_2(esk3_0))
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_55,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k3_relset_1(X36,X37,k3_relset_1(X36,X37,X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_relset_1])])).

fof(c_0_56,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_orders_2(X20,X21,X22)
        | r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))
        | r1_orders_2(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k8_lattice3(esk3_0,esk4_0),u1_struct_0(k7_lattice3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22])])).

cnf(c_0_58,plain,
    ( k8_lattice3(X1,X2) = X2
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k4_relat_1(u1_orders_2(esk3_0)) = k4_relat_1(u1_orders_2(X1))
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k3_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_orders_2(k7_lattice3(esk3_0)))) = k7_lattice3(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk3_0)) = k4_relat_1(u1_orders_2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_22])])).

cnf(c_0_62,plain,
    ( k3_relset_1(X2,X3,k3_relset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k7_lattice3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52]),c_0_22])])).

cnf(c_0_65,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(X1))) = k7_lattice3(esk3_0)
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_59]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k3_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(esk3_0)))) = k7_lattice3(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( k3_relset_1(X1,X2,k4_relat_1(X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r1_orders_2(k7_lattice3(esk3_0),k8_lattice3(esk3_0,esk5_0),k8_lattice3(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(k7_lattice3(esk3_0)))
    | ~ r1_orders_2(k7_lattice3(esk3_0),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(esk3_0)))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_72,plain,(
    ! [X23,X24] :
      ( ( v1_orders_2(g1_orders_2(X23,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) )
      & ( l1_orders_2(g1_orders_2(X23,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_73,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(esk3_0))) = k7_lattice3(esk3_0)
    | k7_lattice3(esk3_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) != g1_orders_2(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) = k7_lattice3(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_66])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(esk3_0),esk5_0,k8_lattice3(esk3_0,esk4_0))
    | ~ r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_70]),c_0_22])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k8_lattice3(esk3_0,esk5_0),u1_struct_0(k7_lattice3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_70]),c_0_22])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(k7_lattice3(esk3_0)))
    | ~ r1_orders_2(k7_lattice3(esk3_0),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_38])).

cnf(c_0_79,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(esk3_0))) = k7_lattice3(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_22])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k4_relat_1(u1_orders_2(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(k7_lattice3(esk3_0),k8_lattice3(esk3_0,esk5_0),k8_lattice3(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_83,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(k4_tarski(X14,X15),X13)
        | r2_hidden(k4_tarski(X15,X14),X12)
        | X13 != k4_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X17,X16),X12)
        | r2_hidden(k4_tarski(X16,X17),X13)
        | X13 != k4_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13)),X13)
        | ~ r2_hidden(k4_tarski(esk2_2(X12,X13),esk1_2(X12,X13)),X12)
        | X13 = k4_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13)),X13)
        | r2_hidden(k4_tarski(esk2_2(X12,X13),esk1_2(X12,X13)),X12)
        | X13 = k4_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

cnf(c_0_84,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | k7_lattice3(k7_lattice3(esk3_0)) != g1_orders_2(X2,X1)
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(esk3_0),esk5_0,esk4_0)
    | ~ r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_58]),c_0_52]),c_0_22])])).

cnf(c_0_86,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k7_lattice3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_58]),c_0_70]),c_0_22])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),k4_relat_1(u1_orders_2(esk3_0)))
    | ~ r1_orders_2(k7_lattice3(esk3_0),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(k7_lattice3(esk3_0),esk5_0,k8_lattice3(esk3_0,esk4_0))
    | r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_58]),c_0_70]),c_0_22])])).

cnf(c_0_91,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_92,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_93,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | k7_lattice3(k7_lattice3(esk3_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_18]),c_0_22])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(k4_tarski(esk5_0,esk4_0),u1_orders_2(k7_lattice3(esk3_0)))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_64]),c_0_87])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),k4_relat_1(u1_orders_2(esk3_0)))
    | ~ r1_orders_2(k7_lattice3(esk3_0),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_96,negated_conjecture,
    ( r1_orders_2(k7_lattice3(esk3_0),esk5_0,esk4_0)
    | r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_58]),c_0_52]),c_0_22])])).

cnf(c_0_97,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(k4_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( k4_relat_1(k3_relset_1(X1,X2,X3)) = X3
    | ~ m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_62])).

cnf(c_0_99,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(esk3_0))) = u1_orders_2(esk3_0)
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_67])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(k4_tarski(esk5_0,esk4_0),k4_relat_1(u1_orders_2(esk3_0)))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_61])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk5_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_70]),c_0_22])])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,esk4_0),k4_relat_1(u1_orders_2(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_70])])).

cnf(c_0_104,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X1),k3_relset_1(X4,X5,X3))
    | ~ m1_subset_1(k3_relset_1(X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(esk3_0))) = u1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_89])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(k4_tarski(esk5_0,esk4_0),k4_relat_1(u1_orders_2(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_89])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),k4_relat_1(u1_orders_2(esk3_0)))
    | r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_52])])).

cnf(c_0_108,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k4_relat_1(u1_orders_2(k7_lattice3(esk3_0)))) = k7_lattice3(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(u1_orders_2(esk3_0)))
    | ~ r2_hidden(k4_tarski(X2,X1),u1_orders_2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_66]),c_0_81])])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),k4_relat_1(k4_relat_1(u1_orders_2(esk3_0)))) = k7_lattice3(k7_lattice3(esk3_0))
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_61])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_109]),c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( k4_relat_1(k4_relat_1(u1_orders_2(esk3_0))) = u1_orders_2(esk3_0)
    | ~ l1_orders_2(k7_lattice3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),k4_relat_1(u1_orders_2(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_103,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( k4_relat_1(k4_relat_1(u1_orders_2(esk3_0))) = u1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_89])])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_86]),c_0_70]),c_0_52]),c_0_22])])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_relat_1(k4_relat_1(u1_orders_2(esk3_0)))
    | ~ v1_relat_1(u1_orders_2(esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_114]),c_0_115]),c_0_115]),c_0_116])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk3_0))
    | ~ m1_subset_1(k4_relat_1(u1_orders_2(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_99])).

cnf(c_0_119,negated_conjecture,
    ( ~ m1_subset_1(k4_relat_1(u1_orders_2(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_99])).

cnf(c_0_120,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_81])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_66,c_0_120]),
    [proof]).

%------------------------------------------------------------------------------
