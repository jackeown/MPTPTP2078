%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 391 expanded)
%              Number of clauses        :   44 ( 179 expanded)
%              Number of leaves         :   13 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 (1053 expanded)
%              Number of equality atoms :   45 ( 166 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

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

fof(dt_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_toler_1)).

fof(t57_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1)
            & m1_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_yellow_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(redefinition_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => k1_toler_1(X1,X2) = k2_wellord1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ( v1_orders_2(g1_orders_2(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( l1_orders_2(g1_orders_2(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(u1_orders_2(X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X19)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X20 = X22
        | g1_orders_2(X20,X21) != g1_orders_2(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X20))) )
      & ( X21 = X23
        | g1_orders_2(X20,X21) != g1_orders_2(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_17,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | m1_subset_1(k1_toler_1(X17,X18),k1_zfmisc_1(k2_zfmisc_1(X18,X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_toler_1])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1)
              & m1_yellow_0(g1_orders_2(X2,k1_toler_1(u1_orders_2(X1),X2)),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_yellow_0])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_28,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_29,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))),u1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_30,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0)
      | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_33,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( u1_orders_2(X1) = u1_orders_2(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_38,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_toler_1(X2,X1))),u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1)))) = g1_orders_2(X1,k1_toler_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_33])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ( ~ v4_yellow_0(X12,X11)
        | u1_orders_2(X12) = k1_toler_1(u1_orders_2(X11),u1_struct_0(X12))
        | ~ m1_yellow_0(X12,X11)
        | ~ l1_orders_2(X11) )
      & ( u1_orders_2(X12) != k1_toler_1(u1_orders_2(X11),u1_struct_0(X12))
        | v4_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

cnf(c_0_40,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( u1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_orders_2(esk1_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(u1_struct_0(X10),u1_struct_0(X9))
        | ~ m1_yellow_0(X10,X9)
        | ~ l1_orders_2(X10)
        | ~ l1_orders_2(X9) )
      & ( r1_tarski(u1_orders_2(X10),u1_orders_2(X9))
        | ~ m1_yellow_0(X10,X9)
        | ~ l1_orders_2(X10)
        | ~ l1_orders_2(X9) )
      & ( ~ r1_tarski(u1_struct_0(X10),u1_struct_0(X9))
        | ~ r1_tarski(u1_orders_2(X10),u1_orders_2(X9))
        | m1_yellow_0(X10,X9)
        | ~ l1_orders_2(X10)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

cnf(c_0_43,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_toler_1(X2,X1))) = X3
    | g1_orders_2(X1,k1_toler_1(X2,X1)) != g1_orders_2(X3,X4)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ v4_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0)
    | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( v4_yellow_0(X1,X2)
    | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0))
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])).

cnf(c_0_47,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_toler_1(X2,X1))) = X1
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1))) = X3
    | g1_orders_2(X1,k1_toler_1(X2,X1)) != g1_orders_2(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_33])).

fof(c_0_50,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_51,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | k2_wellord1(X13,X14) = k3_xboole_0(X13,k2_zfmisc_1(X14,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_52,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk1_0),u1_struct_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)))) != u1_orders_2(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)))
    | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_36])])).

cnf(c_0_54,plain,
    ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | ~ r1_tarski(u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1))),u1_orders_2(X3))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ v1_relat_1(X2)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_33])).

cnf(c_0_55,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_toler_1(X2,X1))) = k1_toler_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_58,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | k1_toler_1(X24,X25) = k2_wellord1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).

cnf(c_0_59,negated_conjecture,
    ( u1_orders_2(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0))) != k1_toler_1(u1_orders_2(esk1_0),esk2_0)
    | ~ m1_yellow_0(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_53])])).

cnf(c_0_60,plain,
    ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(X2,X1)),X3)
    | ~ r1_tarski(k1_toler_1(X2,X1),u1_orders_2(X3))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ v1_relat_1(X2)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_wellord1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k1_toler_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( u1_orders_2(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0))) != k1_toler_1(u1_orders_2(esk1_0),esk2_0)
    | ~ r1_tarski(k1_toler_1(u1_orders_2(esk1_0),esk2_0),u1_orders_2(esk1_0))
    | ~ r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_53]),c_0_36])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_toler_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( u1_orders_2(g1_orders_2(esk2_0,k1_toler_1(u1_orders_2(esk1_0),esk2_0))) != k1_toler_1(u1_orders_2(esk1_0),esk2_0)
    | ~ r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_53])])).

fof(c_0_66,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_55]),c_0_53])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])]),
    [proof]).

%------------------------------------------------------------------------------
