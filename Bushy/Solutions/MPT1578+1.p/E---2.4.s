%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t57_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 1.13s
% Output     : CNFRefutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 205 expanded)
%              Number of clauses        :   43 (  94 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 524 expanded)
%              Number of equality atoms :   39 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',dt_u1_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',t17_xboole_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',abstractness_v1_orders_2)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',dt_g1_orders_2)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',commutativity_k3_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',d6_wellord1)).

fof(redefinition_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => k1_toler_1(X1,X2) = k2_wellord1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',redefinition_k1_toler_1)).

fof(dt_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',dt_k1_toler_1)).

fof(t57_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1)
            & m1_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',t57_yellow_0)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',d14_yellow_0)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',d13_yellow_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t57_yellow_0.p',cc1_relset_1)).

fof(c_0_14,plain,(
    ! [X32,X33,X34,X35] :
      ( ( X32 = X34
        | g1_orders_2(X32,X33) != g1_orders_2(X34,X35)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X32))) )
      & ( X33 = X35
        | g1_orders_2(X32,X33) != g1_orders_2(X34,X35)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_15,plain,(
    ! [X25] :
      ( ~ l1_orders_2(X25)
      | m1_subset_1(u1_orders_2(X25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X25)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_16,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X39,X40] : r1_tarski(k3_xboole_0(X39,X40),X39) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ v1_orders_2(X7)
      | X7 = g1_orders_2(u1_struct_0(X7),u1_orders_2(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( v1_orders_2(g1_orders_2(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) )
      & ( l1_orders_2(g1_orders_2(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_30,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k2_wellord1(X14,X15) = k3_xboole_0(X14,k2_zfmisc_1(X15,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_31,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_32,plain,
    ( v1_orders_2(g1_orders_2(X1,k3_xboole_0(k2_zfmisc_1(X1,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( l1_orders_2(g1_orders_2(X1,k3_xboole_0(k2_zfmisc_1(X1,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( u1_struct_0(g1_orders_2(X1,k3_xboole_0(k2_zfmisc_1(X1,X1),X2))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X1),X2) = k2_wellord1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | k1_toler_1(X37,X38) = k2_wellord1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | m1_subset_1(k1_toler_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X19,X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_toler_1])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1)
              & m1_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_yellow_0])).

fof(c_0_42,plain,(
    ! [X12,X13] :
      ( ( ~ v4_yellow_0(X13,X12)
        | u1_orders_2(X13) = k1_toler_1(u1_orders_2(X12),u1_struct_0(X13))
        | ~ m1_yellow_0(X13,X12)
        | ~ l1_orders_2(X12) )
      & ( u1_orders_2(X13) != k1_toler_1(u1_orders_2(X12),u1_struct_0(X13))
        | v4_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

cnf(c_0_43,plain,
    ( u1_struct_0(g1_orders_2(X1,k2_wellord1(X2,X1))) = X1
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k1_toler_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(u1_struct_0(X11),u1_struct_0(X10))
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( r1_tarski(u1_orders_2(X11),u1_orders_2(X10))
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_tarski(u1_struct_0(X11),u1_struct_0(X10))
        | ~ r1_tarski(u1_orders_2(X11),u1_orders_2(X10))
        | m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_48,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0)
      | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_49,plain,
    ( v4_yellow_0(X1,X2)
    | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_toler_1(X2,X1))) = X1
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( u1_orders_2(g1_orders_2(X1,X2)) = X2
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25])])).

cnf(c_0_52,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_53,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_54,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( ~ v4_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0)
    | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( v4_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | k1_toler_1(u1_orders_2(X3),X1) != u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))
    | ~ v1_relat_1(X2)
    | ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1))) = k1_toler_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1))),u1_orders_2(X3))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_wellord1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk1_0))
    | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])]),c_0_58])).

cnf(c_0_62,plain,
    ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_toler_1(X2,X1),u1_orders_2(X3))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_toler_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

fof(c_0_64,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | v1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk1_0))
    | ~ r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57])]),c_0_63])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_68,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_70,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
