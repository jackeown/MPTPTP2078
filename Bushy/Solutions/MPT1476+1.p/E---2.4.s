%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t9_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:59 EDT 2019

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :  182 (8487 expanded)
%              Number of clauses        :  143 (3873 expanded)
%              Number of leaves         :   19 (2182 expanded)
%              Depth                    :   31
%              Number of atoms          :  512 (22653 expanded)
%              Number of equality atoms :  135 (5716 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',free_g1_orders_2)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',dt_k3_relset_1)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',redefinition_k3_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',dt_u1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',d5_lattice3)).

fof(t9_lattice3,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r1_orders_2(k7_lattice3(X1),k8_lattice3(X1,X3),k8_lattice3(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',t9_lattice3)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',abstractness_v1_orders_2)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',dt_k7_lattice3)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',cc1_relset_1)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',dt_g1_orders_2)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',d7_relat_1)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',d9_orders_2)).

fof(dt_k8_lattice3,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',dt_k8_lattice3)).

fof(d6_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k8_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',d6_lattice3)).

fof(involutiveness_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,k3_relset_1(X1,X2,X3)) = X3 ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',involutiveness_k3_relset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',t7_boole)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',involutiveness_k4_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t9_lattice3.p',t2_subset)).

fof(c_0_19,plain,(
    ! [X40,X41,X42,X43] :
      ( ( X40 = X42
        | g1_orders_2(X40,X41) != g1_orders_2(X42,X43)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X40))) )
      & ( X41 = X43
        | g1_orders_2(X40,X41) != g1_orders_2(X42,X43)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k3_relset_1(X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(X28,X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

fof(c_0_21,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k3_relset_1(X48,X49,X50) = k4_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

fof(c_0_22,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | m1_subset_1(u1_orders_2(X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X35)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | k7_lattice3(X11) = g1_orders_2(u1_struct_0(X11),k3_relset_1(u1_struct_0(X11),u1_struct_0(X11),u1_orders_2(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

cnf(c_0_28,plain,
    ( k3_relset_1(X1,X1,X2) = X3
    | g1_orders_2(X1,k3_relset_1(X1,X1,X2)) != g1_orders_2(X4,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)) = k4_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k4_relat_1(u1_orders_2(X1)) = X2
    | g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26])).

cnf(c_0_32,plain,
    ( g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_orders_2(X1,X2,X3)
                <=> r1_orders_2(k7_lattice3(X1),k8_lattice3(X1,X3),k8_lattice3(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_lattice3])).

cnf(c_0_34,plain,
    ( k4_relat_1(u1_orders_2(X1)) = X2
    | k7_lattice3(X1) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(k7_lattice3(esk1_0),k8_lattice3(esk1_0,esk3_0),k8_lattice3(esk1_0,esk2_0)) )
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_orders_2(k7_lattice3(esk1_0),k8_lattice3(esk1_0,esk3_0),k8_lattice3(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_36,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_26])).

cnf(c_0_38,plain,
    ( k4_relat_1(u1_orders_2(X1)) = k4_relat_1(u1_orders_2(X2))
    | k7_lattice3(X1) != k7_lattice3(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k4_relat_1(u1_orders_2(esk1_0)) = k4_relat_1(u1_orders_2(X1))
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(X2))) != g1_orders_2(X1,X3)
    | k7_lattice3(esk1_0) != k7_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])])).

fof(c_0_43,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_orders_2(X8)
      | X8 = g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_44,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_39])])).

cnf(c_0_46,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X31] :
      ( ( v1_orders_2(k7_lattice3(X31))
        | ~ l1_orders_2(X31) )
      & ( l1_orders_2(k7_lattice3(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_48,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(X1)
    | k7_lattice3(esk1_0) != X1
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | X1 != k7_lattice3(X2)
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(k7_lattice3(X1)) = u1_struct_0(esk1_0)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,plain,
    ( u1_struct_0(k7_lattice3(X1)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_51]),c_0_50])).

fof(c_0_55,plain,(
    ! [X68,X69,X70] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
      | v1_relat_1(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(k7_lattice3(X2)))) != g1_orders_2(X1,X3)
    | k7_lattice3(esk1_0) != k7_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_51])).

cnf(c_0_57,plain,
    ( g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(k7_lattice3(X1)))) = k7_lattice3(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_54]),c_0_51])).

fof(c_0_58,plain,(
    ! [X25,X26] :
      ( ( v1_orders_2(g1_orders_2(X25,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) )
      & ( l1_orders_2(g1_orders_2(X25,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_59,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(k4_tarski(X16,X17),X15)
        | r2_hidden(k4_tarski(X17,X16),X14)
        | X15 != k4_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X19,X18),X14)
        | r2_hidden(k4_tarski(X18,X19),X15)
        | X15 != k4_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X14,X15),esk5_2(X14,X15)),X15)
        | ~ r2_hidden(k4_tarski(esk5_2(X14,X15),esk4_2(X14,X15)),X14)
        | X15 = k4_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk4_2(X14,X15),esk5_2(X14,X15)),X15)
        | r2_hidden(k4_tarski(esk5_2(X14,X15),esk4_2(X14,X15)),X14)
        | X15 = k4_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_61,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r1_orders_2(X22,X23,X24)
        | r2_hidden(k4_tarski(X23,X24),u1_orders_2(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),u1_orders_2(X22))
        | r1_orders_2(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39])])).

cnf(c_0_63,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_64,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( v1_relat_1(k3_relset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_24])).

cnf(c_0_66,plain,
    ( k3_relset_1(X1,X2,k3_relset_1(X2,X1,X3)) = k4_relat_1(k3_relset_1(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k4_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_26])).

fof(c_0_70,plain,(
    ! [X32,X33] :
      ( ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | m1_subset_1(k8_lattice3(X32,X33),u1_struct_0(k7_lattice3(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_lattice3])])).

fof(c_0_71,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | k8_lattice3(X12,X13) = X13 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_lattice3])])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(X1)
    | k7_lattice3(k7_lattice3(esk1_0)) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_32])).

cnf(c_0_73,plain,
    ( u1_orders_2(X1) = X2
    | X1 != g1_orders_2(X3,X2)
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46])).

cnf(c_0_74,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,plain,
    ( l1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_24])).

cnf(c_0_76,plain,
    ( v1_relat_1(k4_relat_1(k3_relset_1(X1,X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_24])).

fof(c_0_77,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k3_relset_1(X44,X45,k3_relset_1(X44,X45,X46)) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_relset_1])])).

cnf(c_0_78,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | u1_orders_2(X4) != k4_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_orders_2(X4,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_79,plain,
    ( m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(k7_lattice3(esk1_0),k8_lattice3(esk1_0,esk3_0),k8_lattice3(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_81,plain,
    ( k8_lattice3(X1,X2) = X2
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = u1_struct_0(esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( u1_orders_2(g1_orders_2(X1,X2)) = X2
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_37])).

cnf(c_0_86,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_26])).

cnf(c_0_87,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(u1_orders_2(X1))))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_29]),c_0_26])).

cnf(c_0_88,plain,
    ( k3_relset_1(X2,X3,k3_relset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,plain,
    ( r2_hidden(k4_tarski(k8_lattice3(X1,X2),X3),X4)
    | u1_orders_2(k7_lattice3(X1)) != k4_relat_1(X4)
    | ~ v1_relat_1(X4)
    | ~ r1_orders_2(k7_lattice3(X1),X3,k8_lattice3(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_51])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(k7_lattice3(esk1_0),esk3_0,k8_lattice3(esk1_0,esk2_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_39])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_51]),c_0_39])])).

cnf(c_0_93,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(X1)))) = k4_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(X1))) = k7_lattice3(esk1_0)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_39])])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(k4_relat_1(k4_relat_1(u1_orders_2(esk1_0))))
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_41])).

cnf(c_0_96,plain,
    ( k4_relat_1(k3_relset_1(X1,X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_66])).

fof(c_0_97,plain,(
    ! [X64,X65] :
      ( ~ r2_hidden(X64,X65)
      | ~ v1_xboole_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k4_tarski(k8_lattice3(esk1_0,esk2_0),esk3_0),X1)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | u1_orders_2(k7_lattice3(esk1_0)) != k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_39])]),c_0_92]),c_0_82])])).

cnf(c_0_99,negated_conjecture,
    ( u1_orders_2(k7_lattice3(esk1_0)) = k4_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_39])])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(k4_relat_1(k4_relat_1(u1_orders_2(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_95]),c_0_39])])).

cnf(c_0_101,plain,
    ( k4_relat_1(k4_relat_1(u1_orders_2(X1))) = u1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_29]),c_0_26])).

cnf(c_0_102,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_104,plain,(
    ! [X47] :
      ( ~ v1_relat_1(X47)
      | k4_relat_1(k4_relat_1(X47)) = X47 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k4_tarski(k8_lattice3(esk1_0,esk2_0),esk3_0),X1)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | k4_relat_1(u1_orders_2(esk1_0)) != k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_39])])).

cnf(c_0_107,plain,
    ( u1_struct_0(X1) = X2
    | X1 != g1_orders_2(X2,X3)
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_108,negated_conjecture,
    ( v1_orders_2(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0))))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_92])).

cnf(c_0_109,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(k7_lattice3(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_54]),c_0_51]),c_0_50])).

cnf(c_0_110,negated_conjecture,
    ( l1_orders_2(g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(esk1_0))))
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_41])).

cnf(c_0_111,plain,
    ( ~ v1_xboole_0(u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_68])).

cnf(c_0_112,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( k4_relat_1(k4_relat_1(u1_orders_2(esk1_0))) = u1_orders_2(X1)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_41])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k4_tarski(k8_lattice3(esk1_0,esk2_0),esk3_0),u1_orders_2(esk1_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_105]),c_0_106])])).

cnf(c_0_115,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_107])).

cnf(c_0_116,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_39])])).

cnf(c_0_118,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_32]),c_0_39])])).

cnf(c_0_119,plain,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) = u1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_29]),c_0_26])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_82]),c_0_39])])).

cnf(c_0_121,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk1_0)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_106])])).

cnf(c_0_122,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),u1_orders_2(esk1_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_81]),c_0_91]),c_0_39])])).

cnf(c_0_124,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_102]),c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])])).

cnf(c_0_126,plain,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_relat_1(u1_orders_2(X1))) = k4_relat_1(k4_relat_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_26])).

cnf(c_0_127,negated_conjecture,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_relat_1(u1_orders_2(esk1_0))) = u1_orders_2(X1)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_41])).

cnf(c_0_128,plain,
    ( v1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_24])).

fof(c_0_129,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | m1_subset_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_130,negated_conjecture,
    ( k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ v1_xboole_0(u1_orders_2(X1))
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_131,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_82]),c_0_91]),c_0_39])])).

cnf(c_0_132,plain,
    ( g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))))) = k7_lattice3(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_124]),c_0_116])).

cnf(c_0_133,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_99]),c_0_92]),c_0_125]),c_0_118])])).

cnf(c_0_134,negated_conjecture,
    ( k4_relat_1(k4_relat_1(u1_orders_2(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_39])])).

cnf(c_0_135,negated_conjecture,
    ( v1_orders_2(g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(k7_lattice3(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_92]),c_0_118])])).

cnf(c_0_136,negated_conjecture,
    ( l1_orders_2(g1_orders_2(u1_struct_0(esk1_0),k4_relat_1(u1_orders_2(k7_lattice3(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_92]),c_0_118])])).

cnf(c_0_137,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | X1 != k7_lattice3(k7_lattice3(X2))
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_54]),c_0_51])).

cnf(c_0_138,plain,
    ( u1_struct_0(g1_orders_2(X1,k3_relset_1(X1,X1,X2))) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_128]),c_0_75])).

cnf(c_0_139,plain,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(k7_lattice3(X1))) = k4_relat_1(u1_orders_2(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_54]),c_0_51])).

cnf(c_0_140,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_54]),c_0_51])).

cnf(c_0_141,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_142,negated_conjecture,
    ( k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ v1_xboole_0(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_91])])).

cnf(c_0_143,plain,
    ( u1_orders_2(k7_lattice3(X1)) = k4_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_32]),c_0_51]),c_0_50])).

cnf(c_0_144,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_99]),c_0_92]),c_0_92]),c_0_133]),c_0_99]),c_0_134]),c_0_92]),c_0_133]),c_0_118])])).

cnf(c_0_145,negated_conjecture,
    ( v1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_57]),c_0_39])])).

cnf(c_0_146,negated_conjecture,
    ( l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_57]),c_0_39])])).

cnf(c_0_147,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(X1))) = u1_struct_0(X1)
    | ~ v1_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_137])).

cnf(c_0_148,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),k4_relat_1(u1_orders_2(k7_lattice3(X1))))) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_140])).

cnf(c_0_149,plain,
    ( m1_subset_1(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_141,c_0_68])).

cnf(c_0_150,negated_conjecture,
    ( k7_lattice3(k7_lattice3(X1)) != k7_lattice3(esk1_0)
    | ~ v1_xboole_0(k4_relat_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_51])).

cnf(c_0_151,negated_conjecture,
    ( u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_144]),c_0_145]),c_0_146])])).

cnf(c_0_152,negated_conjecture,
    ( u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_145]),c_0_146]),c_0_39])])).

cnf(c_0_153,plain,
    ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_81])).

cnf(c_0_154,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(X1))) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_57])).

fof(c_0_155,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X53,X54)
      | v1_xboole_0(X54)
      | r2_hidden(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_156,negated_conjecture,
    ( m1_subset_1(k4_tarski(X1,X2),u1_orders_2(esk1_0))
    | k7_lattice3(esk1_0) != k7_lattice3(X3)
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_149,c_0_121])).

cnf(c_0_157,negated_conjecture,
    ( k7_lattice3(k7_lattice3(k7_lattice3(esk1_0))) != k7_lattice3(esk1_0)
    | ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_99]),c_0_134]),c_0_118])])).

cnf(c_0_158,negated_conjecture,
    ( k7_lattice3(k7_lattice3(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_151]),c_0_152]),c_0_133]),c_0_146])])).

cnf(c_0_159,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_51])).

cnf(c_0_160,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_155])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(k4_tarski(X1,esk3_0),u1_orders_2(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_82]),c_0_39])])).

cnf(c_0_162,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158])])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | k7_lattice3(esk1_0) != k7_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_159,c_0_53])).

cnf(c_0_164,negated_conjecture,
    ( r1_orders_2(X1,X2,X3)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_121])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_0),u1_orders_2(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_162])).

cnf(c_0_166,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(X1))
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_163,c_0_82])).

cnf(c_0_167,negated_conjecture,
    ( r1_orders_2(X1,X2,esk3_0)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_163]),c_0_166])).

cnf(c_0_168,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_37])).

cnf(c_0_169,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(k7_lattice3(esk1_0),k8_lattice3(esk1_0,esk3_0),k8_lattice3(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_170,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,X1),X2)
    | u1_orders_2(esk1_0) != k4_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_82]),c_0_39])])).

cnf(c_0_171,negated_conjecture,
    ( r1_orders_2(X1,esk2_0,esk3_0)
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_131]),c_0_91])])).

cnf(c_0_172,negated_conjecture,
    ( v1_relat_1(k4_relat_1(u1_orders_2(esk1_0)))
    | k7_lattice3(esk1_0) != k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_168,c_0_41])).

cnf(c_0_173,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(esk1_0),esk3_0,k8_lattice3(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_81]),c_0_82]),c_0_39])])).

cnf(c_0_174,negated_conjecture,
    ( r1_orders_2(k7_lattice3(esk1_0),X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k4_relat_1(u1_orders_2(esk1_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_99]),c_0_92]),c_0_92]),c_0_118])])).

cnf(c_0_175,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_0),X1)
    | u1_orders_2(esk1_0) != k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_91]),c_0_39])])).

cnf(c_0_176,negated_conjecture,
    ( v1_relat_1(k4_relat_1(u1_orders_2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_172]),c_0_39])])).

cnf(c_0_177,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(esk1_0),esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_81]),c_0_91]),c_0_39])])).

cnf(c_0_178,negated_conjecture,
    ( r1_orders_2(k7_lattice3(esk1_0),X1,X2)
    | k7_lattice3(esk1_0) != k7_lattice3(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k4_relat_1(u1_orders_2(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_174,c_0_41])).

cnf(c_0_179,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_0),k4_relat_1(u1_orders_2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_134]),c_0_176])])).

cnf(c_0_180,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(esk1_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_177,c_0_131])])).

cnf(c_0_181,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_91]),c_0_82]),c_0_39])]),c_0_180]),
    [proof]).
%------------------------------------------------------------------------------
