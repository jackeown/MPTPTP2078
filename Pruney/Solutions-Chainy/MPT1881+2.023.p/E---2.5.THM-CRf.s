%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:33 EST 2020

% Result     : Theorem 17.66s
% Output     : CNFRefutation 17.66s
% Verified   : 
% Statistics : Number of formulae       :  144 (2172 expanded)
%              Number of clauses        :  109 ( 918 expanded)
%              Number of leaves         :   17 ( 567 expanded)
%              Depth                    :   25
%              Number of atoms          :  508 (7426 expanded)
%              Number of equality atoms :   22 ( 550 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t47_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tex_2(X2,X1) )
           => v1_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t79_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v1_tops_1(X2,X1)
                  & r1_tarski(X2,X3) )
               => v1_tops_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

fof(t48_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_tops_1(X2,X1)
              & v2_tex_2(X2,X1) )
           => v3_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(fc12_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_tops_1(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tex_2(X2,X1)
            <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tex_2])).

fof(c_0_18,plain,(
    ! [X7] :
      ( m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))
      & ~ v1_subset_1(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ( ~ v1_subset_1(X23,X22)
        | X23 != X22
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) )
      & ( X23 = X22
        | v1_subset_1(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ v3_pre_topc(X34,X33)
      | ~ v3_tex_2(X34,X33)
      | v1_tops_1(X34,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v1_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_tex_2(esk5_0,esk4_0)
      | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) )
    & ( v3_tex_2(esk5_0,esk4_0)
      | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_22,plain,
    ( ~ v1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_subset_1(X1,esk1_1(X2))
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0)
    | ~ v3_tex_2(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ( ~ v1_tdlat_3(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v3_pre_topc(X25,X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk2_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | v1_tdlat_3(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ v3_pre_topc(esk2_1(X24),X24)
        | v1_tdlat_3(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_34,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | ~ v1_tdlat_3(X19)
      | v2_pre_topc(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_35,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | m1_subset_1(k2_struct_0(X11),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_36,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_37,negated_conjecture,
    ( v1_subset_1(X1,esk5_0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_38,plain,
    ( ~ v1_subset_1(esk1_1(esk1_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_29]),c_0_30])])).

cnf(c_0_39,plain,
    ( v1_subset_1(esk1_1(X1),X2)
    | ~ v1_subset_1(X2,X1)
    | ~ m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_40,plain,
    ( v1_subset_1(X1,esk1_1(X2))
    | m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk5_0,esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_30])])).

cnf(c_0_47,plain,
    ( ~ v1_subset_1(X1,esk1_1(X1))
    | ~ m1_subset_1(esk1_1(esk1_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk1_1(esk1_1(X1)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_30])])).

fof(c_0_49,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ v1_tops_1(X17,X16)
      | ~ r1_tarski(X17,X18)
      | v1_tops_1(X18,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_tops_1])])])).

cnf(c_0_50,negated_conjecture,
    ( v1_subset_1(X1,esk4_0)
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(X1)
    | v1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0)
    | v1_subset_1(u1_struct_0(esk4_0),X1)
    | ~ v3_pre_topc(esk5_0,esk4_0)
    | ~ v1_subset_1(esk5_0,X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_53,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( v1_subset_1(esk1_1(X1),X2)
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v3_tex_2(esk1_1(esk5_0),esk4_0)
    | ~ v3_pre_topc(esk1_1(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_46]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( v3_tex_2(X1,esk4_0)
    | v1_subset_1(X1,esk5_0)
    | ~ v1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_59,plain,
    ( ~ v1_subset_1(X1,esk1_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_60,plain,
    ( v1_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_50]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk1_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_51]),c_0_30])])).

cnf(c_0_63,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_39]),c_0_30])])).

cnf(c_0_64,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0)
    | v1_subset_1(u1_struct_0(esk4_0),X1)
    | ~ v1_subset_1(esk5_0,X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_27]),c_0_25])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_55]),c_0_30])])).

cnf(c_0_66,plain,
    ( v1_subset_1(X1,u1_struct_0(X2))
    | m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v3_pre_topc(esk1_1(esk5_0),esk4_0)
    | ~ v1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_30])]),c_0_22])).

cnf(c_0_69,plain,
    ( v1_subset_1(esk1_1(X1),X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_23])).

fof(c_0_70,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ v1_tops_1(X36,X35)
      | ~ v2_tex_2(X36,X35)
      | v3_tex_2(X36,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

cnf(c_0_71,negated_conjecture,
    ( v1_tops_1(esk5_0,esk1_1(esk4_0))
    | ~ v1_tops_1(X1,esk1_1(esk4_0))
    | ~ r1_tarski(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_62])).

fof(c_0_73,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | v1_tops_1(k2_struct_0(X15),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc12_tops_1])])).

cnf(c_0_74,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk1_1(esk4_0)))
    | m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0))
    | ~ l1_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( v1_tops_1(k2_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(X1,esk4_0)
    | ~ r1_tarski(X1,k2_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_67]),c_0_27])])).

fof(c_0_77,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_78,plain,(
    ! [X20,X21] :
      ( ( ~ v1_tops_1(X21,X20)
        | k2_pre_topc(X20,X21) = u1_struct_0(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( k2_pre_topc(X20,X21) != u1_struct_0(X20)
        | v1_tops_1(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

fof(c_0_79,plain,(
    ! [X13,X14] :
      ( ( ~ v1_tops_1(X14,X13)
        | k2_pre_topc(X13,X14) = k2_struct_0(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( k2_pre_topc(X13,X14) != k2_struct_0(X13)
        | v1_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_80,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v3_pre_topc(esk1_1(esk5_0),esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_46])])).

cnf(c_0_81,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ v3_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_83,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ v1_tdlat_3(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | v2_tex_2(X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

cnf(c_0_84,negated_conjecture,
    ( v1_tops_1(esk5_0,esk1_1(esk4_0))
    | ~ v1_tops_1(k2_struct_0(esk1_1(esk4_0)),esk1_1(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk1_1(esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_85,plain,
    ( v1_tops_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( v1_tops_1(esk5_0,X1)
    | v1_subset_1(esk4_0,X1)
    | ~ v1_subset_1(esk5_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk1_1(esk4_0)))
    | m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_62])])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(esk1_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_55]),c_0_48])])).

cnf(c_0_89,negated_conjecture,
    ( v1_tops_1(k2_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ r1_tarski(esk1_1(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_46])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_92,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_53]),c_0_54]),c_0_27]),c_0_46])])).

cnf(c_0_94,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_tops_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_26]),c_0_27]),c_0_25])]),c_0_28])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( v1_tops_1(esk5_0,esk1_1(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk1_1(esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_62])])).

cnf(c_0_97,negated_conjecture,
    ( v1_tops_1(esk5_0,esk1_1(esk4_0))
    | m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),c_0_59])).

cnf(c_0_98,negated_conjecture,
    ( v1_tops_1(k2_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_tops_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_101,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_95,c_0_43])).

cnf(c_0_102,negated_conjecture,
    ( v1_tops_1(esk5_0,esk1_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_90]),c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk4_0))
    | v1_subset_1(X1,esk5_0)
    | ~ v3_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_23])).

cnf(c_0_104,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v1_tops_1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_46]),c_0_27])])).

cnf(c_0_105,negated_conjecture,
    ( v1_tops_1(esk1_1(esk5_0),esk4_0)
    | ~ v1_tops_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_54]),c_0_27]),c_0_25])]),c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( v1_tops_1(esk5_0,X1)
    | v1_subset_1(esk1_1(esk4_0),X1)
    | ~ m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_23])).

cnf(c_0_107,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_108,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),X1)
    | v1_subset_1(X2,esk5_0)
    | v1_subset_1(X2,X1)
    | ~ v3_tex_2(X2,esk4_0)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_23])).

cnf(c_0_109,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(esk5_0,esk4_0)
    | ~ v1_tops_1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( v1_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_106]),c_0_30])])).

cnf(c_0_111,plain,
    ( v1_subset_1(X1,esk1_1(X2))
    | ~ v1_subset_1(esk1_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk1_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_107]),c_0_30])])).

cnf(c_0_113,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),esk5_0)
    | ~ v3_tex_2(u1_struct_0(esk4_0),esk4_0)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(ef,[status(thm)],[c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_115,plain,
    ( v1_subset_1(esk1_1(X1),X2)
    | v1_subset_1(X3,X2)
    | ~ v1_subset_1(X3,X1)
    | ~ m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_116,negated_conjecture,
    ( v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))
    | ~ v1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),esk5_0)
    | v1_subset_1(k1_zfmisc_1(esk5_0),X1)
    | ~ v3_tex_2(u1_struct_0(esk4_0),esk4_0)
    | ~ m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_23])).

cnf(c_0_118,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_25]),c_0_110])])).

cnf(c_0_119,plain,
    ( v1_subset_1(X1,X2)
    | ~ v1_subset_1(X1,esk1_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_48]),c_0_38])).

cnf(c_0_120,negated_conjecture,
    ( v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))
    | ~ v1_subset_1(u1_struct_0(esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_39]),c_0_46])])).

cnf(c_0_121,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),esk5_0)
    | v1_subset_1(k1_zfmisc_1(esk5_0),X1)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk4_0)
    | ~ m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_82]),c_0_26]),c_0_118]),c_0_27]),c_0_65])]),c_0_28])).

fof(c_0_122,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | k9_subset_1(X4,X5,X5) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_123,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_tex_2(X28,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ r1_tarski(X29,X28)
        | k9_subset_1(u1_struct_0(X27),X28,k2_pre_topc(X27,X29)) = X29
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))
        | v2_tex_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( r1_tarski(esk3_2(X27,X28),X28)
        | v2_tex_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( k9_subset_1(u1_struct_0(X27),X28,k2_pre_topc(X27,esk3_2(X27,X28))) != esk3_2(X27,X28)
        | v2_tex_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_124,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ v1_subset_1(u1_struct_0(esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_25])])).

cnf(c_0_125,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),esk5_0)
    | v1_subset_1(k1_zfmisc_1(esk5_0),X1)
    | ~ m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_101]),c_0_54]),c_0_27]),c_0_65])]),c_0_28])).

cnf(c_0_126,negated_conjecture,
    ( v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_55]),c_0_46])])).

cnf(c_0_127,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_128,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk4_0))
    | v1_subset_1(esk5_0,X1)
    | ~ v1_subset_1(u1_struct_0(esk4_0),X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_23])).

cnf(c_0_130,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk4_0),esk5_0)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_65]),c_0_63])).

cnf(c_0_131,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_126]),c_0_25])])).

cnf(c_0_132,plain,
    ( k2_pre_topc(X1,X2) = X2
    | v2_struct_0(X1)
    | ~ v2_tex_2(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_92]),c_0_45])).

cnf(c_0_134,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_65])]),c_0_63]),c_0_131])).

cnf(c_0_135,plain,
    ( X1 = u1_struct_0(X2)
    | v2_struct_0(X2)
    | ~ v2_tex_2(k2_pre_topc(X2,X1),X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_132]),c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( v1_subset_1(esk5_0,X1)
    | ~ v2_tex_2(k2_pre_topc(esk4_0,X1),esk4_0)
    | ~ v1_tops_1(X1,esk4_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_25]),c_0_27])])).

cnf(c_0_138,negated_conjecture,
    ( ~ v2_tex_2(k2_pre_topc(esk4_0,esk5_0),esk4_0)
    | ~ r1_tarski(esk5_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_136]),c_0_110]),c_0_25])])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_110])])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_101]),c_0_54]),c_0_27]),c_0_139])]),c_0_28])).

cnf(c_0_141,negated_conjecture,
    ( ~ r1_tarski(esk5_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_91]),c_0_110]),c_0_27]),c_0_25])])).

cnf(c_0_142,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_90]),c_0_25])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_25,c_0_142]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 17.66/17.88  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 17.66/17.88  # and selection function PSelectUnlessUniqMaxPos.
% 17.66/17.88  #
% 17.66/17.88  # Preprocessing time       : 0.029 s
% 17.66/17.88  # Presaturation interreduction done
% 17.66/17.88  
% 17.66/17.88  # Proof found!
% 17.66/17.88  # SZS status Theorem
% 17.66/17.88  # SZS output start CNFRefutation
% 17.66/17.88  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 17.66/17.88  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 17.66/17.88  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 17.66/17.88  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 17.66/17.88  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 17.66/17.88  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 17.66/17.88  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 17.66/17.88  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 17.66/17.88  fof(t79_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&r1_tarski(X2,X3))=>v1_tops_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 17.66/17.88  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 17.66/17.88  fof(fc12_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_tops_1(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_tops_1)).
% 17.66/17.88  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.66/17.88  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 17.66/17.88  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 17.66/17.88  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 17.66/17.88  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 17.66/17.88  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 17.66/17.88  fof(c_0_17, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 17.66/17.88  fof(c_0_18, plain, ![X7]:(m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))&~v1_subset_1(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 17.66/17.88  fof(c_0_19, plain, ![X22, X23]:((~v1_subset_1(X23,X22)|X23!=X22|~m1_subset_1(X23,k1_zfmisc_1(X22)))&(X23=X22|v1_subset_1(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 17.66/17.88  fof(c_0_20, plain, ![X33, X34]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~v3_pre_topc(X34,X33)|~v3_tex_2(X34,X33)|v1_tops_1(X34,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 17.66/17.88  fof(c_0_21, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v1_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v3_tex_2(esk5_0,esk4_0)|v1_subset_1(esk5_0,u1_struct_0(esk4_0)))&(v3_tex_2(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 17.66/17.88  cnf(c_0_22, plain, (~v1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 17.66/17.88  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 17.66/17.88  cnf(c_0_24, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 17.66/17.88  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_29, plain, (v1_subset_1(X1,esk1_1(X2))|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 17.66/17.88  cnf(c_0_30, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 17.66/17.88  cnf(c_0_31, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)|~v3_tex_2(esk5_0,esk4_0)|~v3_pre_topc(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 17.66/17.88  cnf(c_0_32, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  fof(c_0_33, plain, ![X24, X25]:((~v1_tdlat_3(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v3_pre_topc(X25,X24))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&((m1_subset_1(esk2_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|v1_tdlat_3(X24)|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~v3_pre_topc(esk2_1(X24),X24)|v1_tdlat_3(X24)|(~v2_pre_topc(X24)|~l1_pre_topc(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 17.66/17.88  fof(c_0_34, plain, ![X19]:(~l1_pre_topc(X19)|(~v1_tdlat_3(X19)|v2_pre_topc(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 17.66/17.88  fof(c_0_35, plain, ![X11]:(~l1_struct_0(X11)|m1_subset_1(k2_struct_0(X11),k1_zfmisc_1(u1_struct_0(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 17.66/17.88  fof(c_0_36, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 17.66/17.88  cnf(c_0_37, negated_conjecture, (v1_subset_1(X1,esk5_0)|m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 17.66/17.88  cnf(c_0_38, plain, (~v1_subset_1(esk1_1(esk1_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_29]), c_0_30])])).
% 17.66/17.88  cnf(c_0_39, plain, (v1_subset_1(esk1_1(X1),X2)|~v1_subset_1(X2,X1)|~m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 17.66/17.88  cnf(c_0_40, plain, (v1_subset_1(X1,esk1_1(X2))|m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2)))), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 17.66/17.88  cnf(c_0_41, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)|~v3_pre_topc(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 17.66/17.88  cnf(c_0_42, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 17.66/17.88  cnf(c_0_43, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 17.66/17.88  cnf(c_0_44, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 17.66/17.88  cnf(c_0_45, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 17.66/17.88  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_37]), c_0_30])])).
% 17.66/17.88  cnf(c_0_47, plain, (~v1_subset_1(X1,esk1_1(X1))|~m1_subset_1(esk1_1(esk1_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 17.66/17.88  cnf(c_0_48, plain, (m1_subset_1(esk1_1(esk1_1(X1)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_30])])).
% 17.66/17.88  fof(c_0_49, plain, ![X16, X17, X18]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~v1_tops_1(X17,X16)|~r1_tarski(X17,X18)|v1_tops_1(X18,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_tops_1])])])).
% 17.66/17.88  cnf(c_0_50, negated_conjecture, (v1_subset_1(X1,esk4_0)|m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 17.66/17.88  cnf(c_0_51, negated_conjecture, (l1_pre_topc(X1)|v1_subset_1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 17.66/17.88  cnf(c_0_52, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)|v1_subset_1(u1_struct_0(esk4_0),X1)|~v3_pre_topc(esk5_0,esk4_0)|~v1_subset_1(esk5_0,X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 17.66/17.88  cnf(c_0_53, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_42, c_0_43])).
% 17.66/17.88  cnf(c_0_54, negated_conjecture, (v1_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_55, plain, (v1_subset_1(esk1_1(X1),X2)|m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 17.66/17.88  cnf(c_0_56, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 17.66/17.88  cnf(c_0_57, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v3_tex_2(esk1_1(esk5_0),esk4_0)|~v3_pre_topc(esk1_1(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_46]), c_0_26]), c_0_27])]), c_0_28])).
% 17.66/17.88  cnf(c_0_58, negated_conjecture, (v3_tex_2(X1,esk4_0)|v1_subset_1(X1,esk5_0)|~v1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 17.66/17.88  cnf(c_0_59, plain, (~v1_subset_1(X1,esk1_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 17.66/17.88  cnf(c_0_60, plain, (v1_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 17.66/17.88  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_50]), c_0_30])])).
% 17.66/17.88  cnf(c_0_62, negated_conjecture, (l1_pre_topc(esk1_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_51]), c_0_30])])).
% 17.66/17.88  cnf(c_0_63, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_39]), c_0_30])])).
% 17.66/17.88  cnf(c_0_64, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)|v1_subset_1(u1_struct_0(esk4_0),X1)|~v1_subset_1(esk5_0,X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_27]), c_0_25])])).
% 17.66/17.88  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_55]), c_0_30])])).
% 17.66/17.88  cnf(c_0_66, plain, (v1_subset_1(X1,u1_struct_0(X2))|m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 17.66/17.88  cnf(c_0_67, negated_conjecture, (m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 17.66/17.88  cnf(c_0_68, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v3_pre_topc(esk1_1(esk5_0),esk4_0)|~v1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_30])]), c_0_22])).
% 17.66/17.88  cnf(c_0_69, plain, (v1_subset_1(esk1_1(X1),X2)|~v1_subset_1(X1,X2)|~m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_23])).
% 17.66/17.88  fof(c_0_70, plain, ![X35, X36]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~v1_tops_1(X36,X35)|~v2_tex_2(X36,X35)|v3_tex_2(X36,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 17.66/17.88  cnf(c_0_71, negated_conjecture, (v1_tops_1(esk5_0,esk1_1(esk4_0))|~v1_tops_1(X1,esk1_1(esk4_0))|~r1_tarski(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 17.66/17.88  cnf(c_0_72, negated_conjecture, (m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(u1_struct_0(esk1_1(esk4_0))))), inference(spm,[status(thm)],[c_0_56, c_0_62])).
% 17.66/17.88  fof(c_0_73, plain, ![X15]:(~l1_pre_topc(X15)|v1_tops_1(k2_struct_0(X15),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc12_tops_1])])).
% 17.66/17.88  cnf(c_0_74, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 17.66/17.88  cnf(c_0_75, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk1_1(esk4_0)))|m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0))|~l1_struct_0(esk1_1(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_61])).
% 17.66/17.88  cnf(c_0_76, negated_conjecture, (v1_tops_1(k2_struct_0(esk4_0),esk4_0)|~v1_tops_1(X1,esk4_0)|~r1_tarski(X1,k2_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_67]), c_0_27])])).
% 17.66/17.88  fof(c_0_77, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 17.66/17.88  fof(c_0_78, plain, ![X20, X21]:((~v1_tops_1(X21,X20)|k2_pre_topc(X20,X21)=u1_struct_0(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(k2_pre_topc(X20,X21)!=u1_struct_0(X20)|v1_tops_1(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 17.66/17.88  fof(c_0_79, plain, ![X13, X14]:((~v1_tops_1(X14,X13)|k2_pre_topc(X13,X14)=k2_struct_0(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(k2_pre_topc(X13,X14)!=k2_struct_0(X13)|v1_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 17.66/17.88  cnf(c_0_80, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v3_pre_topc(esk1_1(esk5_0),esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_46])])).
% 17.66/17.88  cnf(c_0_81, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~v3_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.66/17.88  cnf(c_0_82, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 17.66/17.88  fof(c_0_83, plain, ![X31, X32]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~v1_tdlat_3(X31)|~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|v2_tex_2(X32,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 17.66/17.88  cnf(c_0_84, negated_conjecture, (v1_tops_1(esk5_0,esk1_1(esk4_0))|~v1_tops_1(k2_struct_0(esk1_1(esk4_0)),esk1_1(esk4_0))|~r1_tarski(k2_struct_0(esk1_1(esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 17.66/17.88  cnf(c_0_85, plain, (v1_tops_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 17.66/17.88  cnf(c_0_86, negated_conjecture, (v1_tops_1(esk5_0,X1)|v1_subset_1(esk4_0,X1)|~v1_subset_1(esk5_0,u1_struct_0(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_74, c_0_23])).
% 17.66/17.88  cnf(c_0_87, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk1_1(esk4_0)))|m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_45]), c_0_62])])).
% 17.66/17.88  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(esk1_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_55]), c_0_48])])).
% 17.66/17.88  cnf(c_0_89, negated_conjecture, (v1_tops_1(k2_struct_0(esk4_0),esk4_0)|~v1_tops_1(esk1_1(esk5_0),esk4_0)|~r1_tarski(esk1_1(esk5_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_46])).
% 17.66/17.88  cnf(c_0_90, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 17.66/17.88  cnf(c_0_91, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 17.66/17.88  cnf(c_0_92, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 17.66/17.88  cnf(c_0_93, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_53]), c_0_54]), c_0_27]), c_0_46])])).
% 17.66/17.88  cnf(c_0_94, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~v2_tex_2(esk5_0,esk4_0)|~v1_tops_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_26]), c_0_27]), c_0_25])]), c_0_28])).
% 17.66/17.88  cnf(c_0_95, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 17.66/17.88  cnf(c_0_96, negated_conjecture, (v1_tops_1(esk5_0,esk1_1(esk4_0))|~r1_tarski(k2_struct_0(esk1_1(esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_62])])).
% 17.66/17.88  cnf(c_0_97, negated_conjecture, (v1_tops_1(esk5_0,esk1_1(esk4_0))|m1_subset_1(k2_struct_0(esk1_1(esk4_0)),k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), c_0_59])).
% 17.66/17.88  cnf(c_0_98, negated_conjecture, (v1_tops_1(k2_struct_0(esk4_0),esk4_0)|~v1_tops_1(esk1_1(esk5_0),esk4_0)|~m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 17.66/17.88  cnf(c_0_99, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 17.66/17.88  cnf(c_0_100, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v2_tex_2(esk5_0,esk4_0)|~v1_tops_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 17.66/17.88  cnf(c_0_101, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_95, c_0_43])).
% 17.66/17.88  cnf(c_0_102, negated_conjecture, (v1_tops_1(esk5_0,esk1_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_90]), c_0_97])).
% 17.66/17.88  cnf(c_0_103, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk4_0))|v1_subset_1(X1,esk5_0)|~v3_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_23])).
% 17.66/17.88  cnf(c_0_104, negated_conjecture, (v1_tops_1(u1_struct_0(esk4_0),esk4_0)|~v1_tops_1(esk1_1(esk5_0),esk4_0)|~v1_tops_1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_46]), c_0_27])])).
% 17.66/17.88  cnf(c_0_105, negated_conjecture, (v1_tops_1(esk1_1(esk5_0),esk4_0)|~v1_tops_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_54]), c_0_27]), c_0_25])]), c_0_28])).
% 17.66/17.88  cnf(c_0_106, negated_conjecture, (v1_tops_1(esk5_0,X1)|v1_subset_1(esk1_1(esk4_0),X1)|~m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_102, c_0_23])).
% 17.66/17.88  cnf(c_0_107, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk4_0))|m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 17.66/17.88  cnf(c_0_108, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),X1)|v1_subset_1(X2,esk5_0)|v1_subset_1(X2,X1)|~v3_tex_2(X2,esk4_0)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_103, c_0_23])).
% 17.66/17.88  cnf(c_0_109, negated_conjecture, (v1_tops_1(u1_struct_0(esk4_0),esk4_0)|~v1_tops_1(esk5_0,esk4_0)|~v1_tops_1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 17.66/17.88  cnf(c_0_110, negated_conjecture, (v1_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_106]), c_0_30])])).
% 17.66/17.88  cnf(c_0_111, plain, (v1_subset_1(X1,esk1_1(X2))|~v1_subset_1(esk1_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(esk1_1(X2)))), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 17.66/17.88  cnf(c_0_112, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk1_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_107]), c_0_30])])).
% 17.66/17.88  cnf(c_0_113, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),esk5_0)|~v3_tex_2(u1_struct_0(esk4_0),esk4_0)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0))), inference(ef,[status(thm)],[c_0_108])).
% 17.66/17.88  cnf(c_0_114, negated_conjecture, (v1_tops_1(u1_struct_0(esk4_0),esk4_0)|~v1_tops_1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 17.66/17.88  cnf(c_0_115, plain, (v1_subset_1(esk1_1(X1),X2)|v1_subset_1(X3,X2)|~v1_subset_1(X3,X1)|~m1_subset_1(esk1_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 17.66/17.88  cnf(c_0_116, negated_conjecture, (v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))|~v1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 17.66/17.88  cnf(c_0_117, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),esk5_0)|v1_subset_1(k1_zfmisc_1(esk5_0),X1)|~v3_tex_2(u1_struct_0(esk4_0),esk4_0)|~m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_113, c_0_23])).
% 17.66/17.88  cnf(c_0_118, negated_conjecture, (v1_tops_1(u1_struct_0(esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_25]), c_0_110])])).
% 17.66/17.88  cnf(c_0_119, plain, (v1_subset_1(X1,X2)|~v1_subset_1(X1,esk1_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_48]), c_0_38])).
% 17.66/17.88  cnf(c_0_120, negated_conjecture, (v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))|~v1_subset_1(u1_struct_0(esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_39]), c_0_46])])).
% 17.66/17.88  cnf(c_0_121, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),esk5_0)|v1_subset_1(k1_zfmisc_1(esk5_0),X1)|~v2_tex_2(u1_struct_0(esk4_0),esk4_0)|~m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk4_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_82]), c_0_26]), c_0_118]), c_0_27]), c_0_65])]), c_0_28])).
% 17.66/17.88  fof(c_0_122, plain, ![X4, X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X4))|k9_subset_1(X4,X5,X5)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 17.66/17.88  fof(c_0_123, plain, ![X27, X28, X29]:((~v2_tex_2(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(~r1_tarski(X29,X28)|k9_subset_1(u1_struct_0(X27),X28,k2_pre_topc(X27,X29))=X29))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v2_tex_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((r1_tarski(esk3_2(X27,X28),X28)|v2_tex_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(k9_subset_1(u1_struct_0(X27),X28,k2_pre_topc(X27,esk3_2(X27,X28)))!=esk3_2(X27,X28)|v2_tex_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 17.66/17.88  cnf(c_0_124, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~v1_subset_1(u1_struct_0(esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_25])])).
% 17.66/17.88  cnf(c_0_125, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),esk5_0)|v1_subset_1(k1_zfmisc_1(esk5_0),X1)|~m1_subset_1(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk4_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_101]), c_0_54]), c_0_27]), c_0_65])]), c_0_28])).
% 17.66/17.88  cnf(c_0_126, negated_conjecture, (v1_subset_1(esk5_0,esk1_1(u1_struct_0(esk4_0)))|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_55]), c_0_46])])).
% 17.66/17.88  cnf(c_0_127, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 17.66/17.88  cnf(c_0_128, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 17.66/17.88  cnf(c_0_129, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk4_0))|v1_subset_1(esk5_0,X1)|~v1_subset_1(u1_struct_0(esk4_0),X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_124, c_0_23])).
% 17.66/17.88  cnf(c_0_130, negated_conjecture, (v1_subset_1(u1_struct_0(esk4_0),esk5_0)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_65]), c_0_63])).
% 17.66/17.88  cnf(c_0_131, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_126]), c_0_25])])).
% 17.66/17.88  cnf(c_0_132, plain, (k2_pre_topc(X1,X2)=X2|v2_struct_0(X1)|~v2_tex_2(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r1_tarski(X2,k2_pre_topc(X1,X2))|~m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 17.66/17.88  cnf(c_0_133, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_92]), c_0_45])).
% 17.66/17.88  cnf(c_0_134, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_65])]), c_0_63]), c_0_131])).
% 17.66/17.88  cnf(c_0_135, plain, (X1=u1_struct_0(X2)|v2_struct_0(X2)|~v2_tex_2(k2_pre_topc(X2,X1),X2)|~v2_pre_topc(X2)|~v1_tops_1(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,k2_pre_topc(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_132]), c_0_133])).
% 17.66/17.88  cnf(c_0_136, negated_conjecture, (v1_subset_1(esk5_0,X1)|~v2_tex_2(k2_pre_topc(esk4_0,X1),esk4_0)|~v1_tops_1(X1,esk4_0)|~r1_tarski(X1,k2_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_26]), c_0_27])]), c_0_28])).
% 17.66/17.88  cnf(c_0_137, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v1_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_25]), c_0_27])])).
% 17.66/17.88  cnf(c_0_138, negated_conjecture, (~v2_tex_2(k2_pre_topc(esk4_0,esk5_0),esk4_0)|~r1_tarski(esk5_0,k2_pre_topc(esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_136]), c_0_110]), c_0_25])])).
% 17.66/17.88  cnf(c_0_139, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_110])])).
% 17.66/17.89  cnf(c_0_140, negated_conjecture, (~r1_tarski(esk5_0,k2_pre_topc(esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_101]), c_0_54]), c_0_27]), c_0_139])]), c_0_28])).
% 17.66/17.89  cnf(c_0_141, negated_conjecture, (~r1_tarski(esk5_0,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_91]), c_0_110]), c_0_27]), c_0_25])])).
% 17.66/17.89  cnf(c_0_142, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_90]), c_0_25])])).
% 17.66/17.89  cnf(c_0_143, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_25, c_0_142]), ['proof']).
% 17.66/17.89  # SZS output end CNFRefutation
% 17.66/17.89  # Proof object total steps             : 144
% 17.66/17.89  # Proof object clause steps            : 109
% 17.66/17.89  # Proof object formula steps           : 35
% 17.66/17.89  # Proof object conjectures             : 72
% 17.66/17.89  # Proof object clause conjectures      : 69
% 17.66/17.89  # Proof object formula conjectures     : 3
% 17.66/17.89  # Proof object initial clauses used    : 24
% 17.66/17.89  # Proof object initial formulas used   : 17
% 17.66/17.89  # Proof object generating inferences   : 79
% 17.66/17.89  # Proof object simplifying inferences  : 126
% 17.66/17.89  # Training examples: 0 positive, 0 negative
% 17.66/17.89  # Parsed axioms                        : 17
% 17.66/17.89  # Removed by relevancy pruning/SinE    : 0
% 17.66/17.89  # Initial clauses                      : 33
% 17.66/17.89  # Removed in clause preprocessing      : 0
% 17.66/17.89  # Initial clauses in saturation        : 33
% 17.66/17.89  # Processed clauses                    : 98396
% 17.66/17.89  # ...of these trivial                  : 4151
% 17.66/17.89  # ...subsumed                          : 76523
% 17.66/17.89  # ...remaining for further processing  : 17722
% 17.66/17.89  # Other redundant clauses eliminated   : 1024
% 17.66/17.89  # Clauses deleted for lack of memory   : 0
% 17.66/17.89  # Backward-subsumed                    : 1608
% 17.66/17.89  # Backward-rewritten                   : 680
% 17.66/17.89  # Generated clauses                    : 1410914
% 17.66/17.89  # ...of the previous two non-trivial   : 1319455
% 17.66/17.89  # Contextual simplify-reflections      : 1326
% 17.66/17.89  # Paramodulations                      : 1405556
% 17.66/17.89  # Factorizations                       : 4202
% 17.66/17.89  # Equation resolutions                 : 1024
% 17.66/17.89  # Propositional unsat checks           : 0
% 17.66/17.89  #    Propositional check models        : 0
% 17.66/17.89  #    Propositional check unsatisfiable : 0
% 17.66/17.89  #    Propositional clauses             : 0
% 17.66/17.89  #    Propositional clauses after purity: 0
% 17.66/17.89  #    Propositional unsat core size     : 0
% 17.66/17.89  #    Propositional preprocessing time  : 0.000
% 17.66/17.89  #    Propositional encoding time       : 0.000
% 17.66/17.89  #    Propositional solver time         : 0.000
% 17.66/17.89  #    Success case prop preproc time    : 0.000
% 17.66/17.89  #    Success case prop encoding time   : 0.000
% 17.66/17.89  #    Success case prop solver time     : 0.000
% 17.66/17.89  # Current number of processed clauses  : 15268
% 17.66/17.89  #    Positive orientable unit clauses  : 1184
% 17.66/17.89  #    Positive unorientable unit clauses: 0
% 17.66/17.89  #    Negative unit clauses             : 51
% 17.66/17.89  #    Non-unit-clauses                  : 14033
% 17.66/17.89  # Current number of unprocessed clauses: 1207069
% 17.66/17.89  # ...number of literals in the above   : 7105407
% 17.66/17.89  # Current number of archived formulas  : 0
% 17.66/17.89  # Current number of archived clauses   : 2453
% 17.66/17.89  # Clause-clause subsumption calls (NU) : 29474229
% 17.66/17.89  # Rec. Clause-clause subsumption calls : 8185565
% 17.66/17.89  # Non-unit clause-clause subsumptions  : 73239
% 17.66/17.89  # Unit Clause-clause subsumption calls : 128692
% 17.66/17.89  # Rewrite failures with RHS unbound    : 0
% 17.66/17.89  # BW rewrite match attempts            : 44290
% 17.66/17.89  # BW rewrite match successes           : 136
% 17.66/17.89  # Condensation attempts                : 0
% 17.66/17.89  # Condensation successes               : 0
% 17.66/17.89  # Termbank termtop insertions          : 38672152
% 17.75/17.93  
% 17.75/17.93  # -------------------------------------------------
% 17.75/17.93  # User time                : 17.041 s
% 17.75/17.93  # System time              : 0.543 s
% 17.75/17.93  # Total time               : 17.584 s
% 17.75/17.93  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
