%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1941+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:03 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 974 expanded)
%              Number of clauses        :   45 ( 385 expanded)
%              Number of leaves         :   10 ( 245 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 (4607 expanded)
%              Number of equality atoms :   36 ( 445 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d17_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k9_yellow_6(X1,X2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_yellow_6)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(t39_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(t12_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(fraenkel_a_2_0_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_yellow_6(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & r2_hidden(X3,X4)
            & v3_pre_topc(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | k9_yellow_6(X6,X7) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X6,X7))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_yellow_6])])])])).

fof(c_0_11,plain,(
    ! [X8] : k2_yellow_1(X8) = g1_orders_2(X8,k1_yellow_1(X8)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
                <=> ( r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_yellow_6])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | k9_yellow_6(X1,X2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
      | ~ r2_hidden(esk3_0,esk4_0)
      | ~ v3_pre_topc(esk4_0,esk2_0) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) )
    & ( v3_pre_topc(esk4_0,esk2_0)
      | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_16,plain,(
    ! [X10] :
      ( v1_orders_2(k2_yellow_1(X10))
      & l1_orders_2(k2_yellow_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X16 = X18
        | g1_orders_2(X16,X17) != g1_orders_2(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) )
      & ( X17 = X19
        | g1_orders_2(X16,X17) != g1_orders_2(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_18,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_19,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | u1_struct_0(X21) = u1_struct_0(k7_lattice3(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_yellow_6])])).

cnf(c_0_20,plain,
    ( k9_yellow_6(X1,X2) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X1,X2),k1_yellow_1(a_2_0_yellow_6(X1,X2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X9] :
      ( v1_relat_2(k1_yellow_1(X9))
      & v4_relat_2(k1_yellow_1(X9))
      & v8_relat_2(k1_yellow_1(X9))
      & v1_partfun1(k1_yellow_1(X9),X9)
      & m1_subset_1(k1_yellow_1(X9),k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

cnf(c_0_30,plain,
    ( u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(esk2_0,esk3_0),k1_yellow_1(a_2_0_yellow_6(esk2_0,esk3_0)))) = k9_yellow_6(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_32,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_33,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_34,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_14])).

cnf(c_0_35,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X11,X12,X13,X15] :
      ( ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X11,a_2_0_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12)) )
      & ( X11 = esk1_3(X11,X12,X13)
        | ~ r2_hidden(X11,a_2_0_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12)) )
      & ( r2_hidden(X13,esk1_3(X11,X12,X13))
        | ~ r2_hidden(X11,a_2_0_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12)) )
      & ( v3_pre_topc(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(X11,a_2_0_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12)) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | X11 != X15
        | ~ r2_hidden(X13,X15)
        | ~ v3_pre_topc(X15,X12)
        | r2_hidden(X11,a_2_0_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow_6])])])])])])).

fof(c_0_37,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(g1_orders_2(a_2_0_yellow_6(esk2_0,esk3_0),k1_yellow_1(a_2_0_yellow_6(esk2_0,esk3_0)))) = u1_struct_0(k9_yellow_6(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_32])])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,a_2_0_yellow_6(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X1
    | ~ r2_hidden(X4,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k9_yellow_6(esk2_0,esk3_0)) = a_2_0_yellow_6(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk1_3(X1,esk2_0,esk3_0),esk2_0)
    | ~ r2_hidden(X1,a_2_0_yellow_6(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | r2_hidden(esk4_0,a_2_0_yellow_6(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( esk1_3(X1,esk2_0,esk3_0) = X1
    | ~ r2_hidden(X1,a_2_0_yellow_6(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_0_yellow_6(esk2_0,X1))
    | ~ v3_pre_topc(esk4_0,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk4_0,esk2_0,esk3_0),esk2_0)
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk1_3(esk4_0,esk2_0,esk3_0) = esk4_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk2_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_44]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_0_yellow_6(esk2_0,esk3_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | v2_struct_0(X3)
    | ~ r2_hidden(X2,a_2_0_yellow_6(X3,X1))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk4_0,esk2_0,esk3_0) = esk4_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(X1,esk2_0,esk3_0))
    | ~ r2_hidden(X1,a_2_0_yellow_6(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_0_yellow_6(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk1_3(esk4_0,esk2_0,esk3_0) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_60]),
    [proof]).

%------------------------------------------------------------------------------
