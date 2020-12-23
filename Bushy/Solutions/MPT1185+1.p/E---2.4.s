%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t136_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  185 ( 453 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t136_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v6_orders_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => r3_orders_1(u1_orders_2(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t136_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t3_subset)).

fof(t94_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r4_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r4_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t94_orders_1)).

fof(t95_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r8_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r8_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t95_orders_1)).

fof(d8_orders_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r3_orders_1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d8_orders_1)).

fof(t92_orders_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r7_relat_2(X2,X1)
      <=> ( r1_relat_2(X2,X1)
          & r6_relat_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t92_orders_1)).

fof(d6_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
      <=> r4_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d6_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d11_orders_2)).

fof(d5_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v4_orders_2(X1)
      <=> r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d5_orders_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',dt_u1_orders_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r3_orders_1(u1_orders_2(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t136_orders_2])).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & v6_orders_2(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r3_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ r4_relat_2(X45,X43)
      | ~ r1_tarski(X44,X43)
      | r4_relat_2(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_orders_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ r8_relat_2(X48,X46)
      | ~ r1_tarski(X47,X46)
      | r8_relat_2(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_orders_1])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ( r1_relat_2(X13,X14)
        | ~ r3_orders_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r8_relat_2(X13,X14)
        | ~ r3_orders_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r4_relat_2(X13,X14)
        | ~ r3_orders_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r6_relat_2(X13,X14)
        | ~ r3_orders_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_relat_2(X13,X14)
        | ~ r8_relat_2(X13,X14)
        | ~ r4_relat_2(X13,X14)
        | ~ r6_relat_2(X13,X14)
        | r3_orders_1(X13,X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_orders_1])])])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ( r1_relat_2(X39,X38)
        | ~ r7_relat_2(X39,X38)
        | ~ v1_relat_1(X39) )
      & ( r6_relat_2(X39,X38)
        | ~ r7_relat_2(X39,X38)
        | ~ v1_relat_1(X39) )
      & ( ~ r1_relat_2(X39,X38)
        | ~ r6_relat_2(X39,X38)
        | r7_relat_2(X39,X38)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).

cnf(c_0_20,plain,
    ( r4_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r4_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X12] :
      ( ( ~ v5_orders_2(X12)
        | r4_relat_2(u1_orders_2(X12),u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r4_relat_2(u1_orders_2(X12),u1_struct_0(X12))
        | v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_orders_2])])])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ( ~ v6_orders_2(X9,X8)
        | r7_relat_2(u1_orders_2(X8),X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) )
      & ( ~ r7_relat_2(u1_orders_2(X8),X9)
        | v6_orders_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_24,plain,
    ( r8_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X11] :
      ( ( ~ v4_orders_2(X11)
        | r8_relat_2(u1_orders_2(X11),u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r8_relat_2(u1_orders_2(X11),u1_struct_0(X11))
        | v4_orders_2(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_26,plain,
    ( r3_orders_1(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r6_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r4_relat_2(X1,esk2_0)
    | ~ v1_relat_1(X1)
    | ~ r4_relat_2(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v6_orders_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r8_relat_2(X1,esk2_0)
    | ~ v1_relat_1(X1)
    | ~ r8_relat_2(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_36,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | v1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_39,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(u1_orders_2(X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X16)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_40,plain,
    ( r3_orders_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r4_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r4_relat_2(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_34]),c_0_31])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r3_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31]),c_0_37])])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
