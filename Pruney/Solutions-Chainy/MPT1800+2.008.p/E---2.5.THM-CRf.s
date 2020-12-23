%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  102 (2285 expanded)
%              Number of clauses        :   73 ( 788 expanded)
%              Number of leaves         :   14 ( 573 expanded)
%              Depth                    :   21
%              Number of atoms          :  368 (14299 expanded)
%              Number of equality atoms :   69 (2311 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ( u1_struct_0(k8_tmap_1(X20,X21)) = u1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | X22 != u1_struct_0(X21)
        | u1_pre_topc(k8_tmap_1(X20,X21)) = k5_tmap_1(X20,X22)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( ~ v1_tsep_1(esk3_0,esk2_0)
      | ~ m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) )
    & ( v1_tsep_1(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) )
    & ( m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( v2_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( l1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_19,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( ~ v3_pre_topc(X9,X8)
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(X9,u1_pre_topc(X8))
        | v3_pre_topc(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(esk2_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(u1_struct_0(X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22])])).

fof(c_0_33,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | m1_pre_topc(X25,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_34,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_35,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_36,plain,(
    ! [X18,X19] :
      ( ( ~ r2_hidden(X19,u1_pre_topc(X18))
        | u1_pre_topc(X18) = k5_tmap_1(X18,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( u1_pre_topc(X18) != k5_tmap_1(X18,X19)
        | r2_hidden(X19,u1_pre_topc(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_38,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_27])).

fof(c_0_46,plain,(
    ! [X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v3_pre_topc(k2_struct_0(X11),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_47,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k2_struct_0(X7) = u1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_48,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_49,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(esk2_0)) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21]),c_0_22]),c_0_44])]),c_0_24])).

cnf(c_0_50,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X1,X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_51,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | ~ v1_pre_topc(X6)
      | X6 = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_55,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_56,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) = u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(esk2_0,esk2_0)),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk2_0)
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( u1_struct_0(k8_tmap_1(X1,X1)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_38])).

fof(c_0_62,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tsep_1(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != u1_struct_0(X13)
        | v3_pre_topc(X14,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( esk1_2(X12,X13) = u1_struct_0(X13)
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(esk1_2(X12,X13),X12)
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_63,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_20])])).

cnf(c_0_64,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk2_0)
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_65,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_66,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != k8_tmap_1(esk2_0,esk2_0)
    | ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k8_tmap_1(X1,X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_71,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) = u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_73,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_65]),c_0_27])).

cnf(c_0_74,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_27])).

cnf(c_0_75,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != k8_tmap_1(esk2_0,esk2_0)
    | ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = k8_tmap_1(esk2_0,esk2_0)
    | v1_tsep_1(esk3_0,esk2_0)
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_64])).

cnf(c_0_79,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_81,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_22])])).

cnf(c_0_83,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X1))) = k8_tmap_1(X1,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_61]),c_0_69]),c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != k8_tmap_1(esk2_0,esk2_0)
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_76]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = k8_tmap_1(esk2_0,esk2_0)
    | v1_tsep_1(esk3_0,esk2_0)
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_76]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_86,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_27])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_27]),c_0_20]),c_0_22])])).

cnf(c_0_88,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0)
    | u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_72]),c_0_20]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_58]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_20]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0)
    | k8_tmap_1(esk2_0,esk3_0) != k8_tmap_1(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = k8_tmap_1(esk2_0,esk2_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_69]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_20]),c_0_22])])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_88]),c_0_28]),c_0_89]),c_0_90]),c_0_29])]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = k8_tmap_1(esk2_0,esk2_0)
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_92]),c_0_72]),c_0_20]),c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = k8_tmap_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_95]),c_0_28]),c_0_89]),c_0_90]),c_0_29])])).

cnf(c_0_98,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_99,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_58])])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_97])])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_20]),c_0_22])]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.19/0.50  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.048 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.19/0.50  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.19/0.50  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.19/0.50  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.50  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.50  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.50  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.50  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.50  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.19/0.50  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.19/0.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.50  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.19/0.50  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.19/0.50  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.19/0.50  fof(c_0_15, plain, ![X20, X21, X22]:((u1_struct_0(k8_tmap_1(X20,X21))=u1_struct_0(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X22!=u1_struct_0(X21)|u1_pre_topc(k8_tmap_1(X20,X21))=k5_tmap_1(X20,X22))|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.19/0.50  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0))&((v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0))&(m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.19/0.50  fof(c_0_17, plain, ![X16, X17]:(((v1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))&(v2_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16))))&(l1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.19/0.50  fof(c_0_18, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.50  cnf(c_0_19, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_25, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  fof(c_0_26, plain, ![X8, X9]:((~v3_pre_topc(X9,X8)|r2_hidden(X9,u1_pre_topc(X8))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(~r2_hidden(X9,u1_pre_topc(X8))|v3_pre_topc(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.50  cnf(c_0_27, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_28, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.19/0.50  cnf(c_0_29, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_30, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_31, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.50  cnf(c_0_32, negated_conjecture, (r2_hidden(u1_struct_0(X1),u1_pre_topc(esk2_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(u1_struct_0(X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22])])).
% 0.19/0.50  fof(c_0_33, plain, ![X25]:(~l1_pre_topc(X25)|m1_pre_topc(X25,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.50  fof(c_0_34, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.50  fof(c_0_35, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.50  fof(c_0_36, plain, ![X18, X19]:((~r2_hidden(X19,u1_pre_topc(X18))|u1_pre_topc(X18)=k5_tmap_1(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(u1_pre_topc(X18)!=k5_tmap_1(X18,X19)|r2_hidden(X19,u1_pre_topc(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.19/0.50  cnf(c_0_37, negated_conjecture, (r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.19/0.50  cnf(c_0_38, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_39, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_40, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_41, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_42, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.50  cnf(c_0_43, negated_conjecture, (r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29])])).
% 0.19/0.50  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.50  cnf(c_0_45, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_27])).
% 0.19/0.50  fof(c_0_46, plain, ![X11]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|v3_pre_topc(k2_struct_0(X11),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.19/0.50  fof(c_0_47, plain, ![X7]:(~l1_struct_0(X7)|k2_struct_0(X7)=u1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.50  fof(c_0_48, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(esk2_0))=u1_pre_topc(esk2_0)|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21]), c_0_22]), c_0_44])]), c_0_24])).
% 0.19/0.50  cnf(c_0_50, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(k8_tmap_1(X1,X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_38])).
% 0.19/0.50  cnf(c_0_51, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.50  cnf(c_0_52, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.50  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.50  fof(c_0_54, plain, ![X6]:(~l1_pre_topc(X6)|(~v1_pre_topc(X6)|X6=g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk2_0))=u1_pre_topc(esk2_0)|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_56, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.50  cnf(c_0_57, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk2_0))=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_22])])).
% 0.19/0.50  cnf(c_0_59, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_60, negated_conjecture, (g1_pre_topc(u1_struct_0(k8_tmap_1(esk2_0,esk2_0)),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk2_0)|~v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.50  cnf(c_0_61, plain, (u1_struct_0(k8_tmap_1(X1,X1))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_38])).
% 0.19/0.50  fof(c_0_62, plain, ![X12, X13, X14]:((~v1_tsep_1(X13,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(X14!=u1_struct_0(X13)|v3_pre_topc(X14,X12)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((esk1_2(X12,X13)=u1_struct_0(X13)|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&(~v3_pre_topc(esk1_2(X12,X13),X12)|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_20])])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk2_0)|~v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_65, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.19/0.50  cnf(c_0_66, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_67, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=k8_tmap_1(esk2_0,esk2_0)|~v1_tsep_1(esk3_0,esk2_0)|~v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.50  cnf(c_0_69, plain, (v2_struct_0(X1)|l1_pre_topc(k8_tmap_1(X1,X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_71, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(esk3_0))=u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_20]), c_0_21]), c_0_22])]), c_0_24]), c_0_23])).
% 0.19/0.50  cnf(c_0_73, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_65]), c_0_27])).
% 0.19/0.50  cnf(c_0_74, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_27])).
% 0.19/0.50  cnf(c_0_75, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_76, plain, (v2_struct_0(X1)|v1_pre_topc(k8_tmap_1(X1,X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_67, c_0_38])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=k8_tmap_1(esk2_0,esk2_0)|~v1_tsep_1(esk3_0,esk2_0)|~v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=k8_tmap_1(esk2_0,esk2_0)|v1_tsep_1(esk3_0,esk2_0)|~v1_pre_topc(k8_tmap_1(esk2_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_70, c_0_64])).
% 0.19/0.50  cnf(c_0_79, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_80, negated_conjecture, (r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_81, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(X1)|v2_struct_0(X1)|~v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.50  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_22])])).
% 0.19/0.50  cnf(c_0_83, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X1)))=k8_tmap_1(X1,X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_61]), c_0_69]), c_0_76])).
% 0.19/0.50  cnf(c_0_84, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=k8_tmap_1(esk2_0,esk2_0)|~v1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_76]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_85, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=k8_tmap_1(esk2_0,esk2_0)|v1_tsep_1(esk3_0,esk2_0)|~l1_pre_topc(k8_tmap_1(esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_76]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_86, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_79, c_0_27])).
% 0.19/0.50  cnf(c_0_87, negated_conjecture, (r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_27]), c_0_20]), c_0_22])])).
% 0.19/0.50  cnf(c_0_88, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)|u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_72]), c_0_20]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_58]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_90, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_20]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_91, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)|k8_tmap_1(esk2_0,esk3_0)!=k8_tmap_1(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_82])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=k8_tmap_1(esk2_0,esk2_0)|v1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_69]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_93, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_20]), c_0_22])])).
% 0.19/0.50  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_88]), c_0_28]), c_0_89]), c_0_90]), c_0_29])]), c_0_91])).
% 0.19/0.50  cnf(c_0_95, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=k8_tmap_1(esk2_0,esk2_0)|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_92]), c_0_72]), c_0_20]), c_0_21]), c_0_22])]), c_0_24])).
% 0.19/0.50  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.50  cnf(c_0_97, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=k8_tmap_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_95]), c_0_28]), c_0_89]), c_0_90]), c_0_29])])).
% 0.19/0.50  cnf(c_0_98, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_99, negated_conjecture, (v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_58])])).
% 0.19/0.50  cnf(c_0_100, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_97])])).
% 0.19/0.50  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_20]), c_0_22])]), c_0_100]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 102
% 0.19/0.50  # Proof object clause steps            : 73
% 0.19/0.50  # Proof object formula steps           : 29
% 0.19/0.50  # Proof object conjectures             : 44
% 0.19/0.50  # Proof object clause conjectures      : 41
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 26
% 0.19/0.50  # Proof object initial formulas used   : 14
% 0.19/0.50  # Proof object generating inferences   : 40
% 0.19/0.50  # Proof object simplifying inferences  : 116
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 14
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 29
% 0.19/0.50  # Removed in clause preprocessing      : 1
% 0.19/0.50  # Initial clauses in saturation        : 28
% 0.19/0.50  # Processed clauses                    : 1098
% 0.19/0.50  # ...of these trivial                  : 38
% 0.19/0.50  # ...subsumed                          : 561
% 0.19/0.50  # ...remaining for further processing  : 499
% 0.19/0.50  # Other redundant clauses eliminated   : 2
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 111
% 0.19/0.50  # Backward-rewritten                   : 179
% 0.19/0.50  # Generated clauses                    : 2454
% 0.19/0.50  # ...of the previous two non-trivial   : 1807
% 0.19/0.50  # Contextual simplify-reflections      : 80
% 0.19/0.50  # Paramodulations                      : 2451
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 2
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 179
% 0.19/0.50  #    Positive orientable unit clauses  : 19
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 4
% 0.19/0.50  #    Non-unit-clauses                  : 156
% 0.19/0.50  # Current number of unprocessed clauses: 683
% 0.19/0.50  # ...number of literals in the above   : 3870
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 319
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 26711
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 6081
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 725
% 0.19/0.50  # Unit Clause-clause subsumption calls : 557
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 18
% 0.19/0.50  # BW rewrite match successes           : 17
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 66697
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.163 s
% 0.19/0.50  # System time              : 0.005 s
% 0.19/0.50  # Total time               : 0.168 s
% 0.19/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
