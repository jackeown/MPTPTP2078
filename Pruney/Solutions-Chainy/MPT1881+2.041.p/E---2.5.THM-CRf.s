%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:36 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   87 (1330 expanded)
%              Number of clauses        :   66 ( 532 expanded)
%              Number of leaves         :   10 ( 328 expanded)
%              Depth                    :   22
%              Number of atoms          :  293 (5521 expanded)
%              Number of equality atoms :    9 ( 131 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

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

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(fc12_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_tops_1(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,plain,(
    ! [X17] :
      ( ~ l1_struct_0(X17)
      | m1_subset_1(k2_struct_0(X17),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_11,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_12,negated_conjecture,(
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

cnf(c_0_13,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_tex_2(esk4_0,esk3_0)
      | v1_subset_1(esk4_0,u1_struct_0(esk3_0)) )
    & ( v3_tex_2(esk4_0,esk3_0)
      | ~ v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X46,X47] :
      ( v2_struct_0(X46)
      | ~ v2_pre_topc(X46)
      | ~ v1_tdlat_3(X46)
      | ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | v2_tex_2(X47,X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X37,X38] :
      ( ( ~ v1_subset_1(X38,X37)
        | X38 != X37
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) )
      & ( X38 = X37
        | v1_subset_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_20,plain,(
    ! [X48,X49] :
      ( v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | ~ v1_tops_1(X49,X48)
      | ~ v2_tex_2(X49,X48)
      | v3_tex_2(X49,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X19] :
      ( ~ l1_struct_0(X19)
      | ~ v1_subset_1(k2_struct_0(X19),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_18])])).

cnf(c_0_30,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk3_0))
    | m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v3_tex_2(X1,esk3_0)
    | ~ v1_tops_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_24]),c_0_18])]),c_0_29])).

fof(c_0_33,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | v1_tops_1(k2_struct_0(X31),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc12_tops_1])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(k2_struct_0(esk3_0)))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])])).

cnf(c_0_35,negated_conjecture,
    ( v3_tex_2(k2_struct_0(esk3_0),esk3_0)
    | ~ v1_tops_1(k2_struct_0(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_36,plain,
    ( v1_tops_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(k2_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_14]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( v3_tex_2(k2_struct_0(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_18])])).

fof(c_0_39,plain,(
    ! [X39,X40,X41] :
      ( ( v2_tex_2(X40,X39)
        | ~ v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ v2_tex_2(X41,X39)
        | ~ r1_tarski(X40,X41)
        | X40 = X41
        | ~ v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(esk1_2(X39,X40),k1_zfmisc_1(u1_struct_0(X39)))
        | ~ v2_tex_2(X40,X39)
        | v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( v2_tex_2(esk1_2(X39,X40),X39)
        | ~ v2_tex_2(X40,X39)
        | v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( r1_tarski(X40,esk1_2(X39,X40))
        | ~ v2_tex_2(X40,X39)
        | v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( X40 != esk1_2(X39,X40)
        | ~ v2_tex_2(X40,X39)
        | v3_tex_2(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_40,negated_conjecture,
    ( v1_subset_1(k2_struct_0(esk3_0),X1)
    | m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v3_tex_2(X1,esk3_0)
    | v1_subset_1(k2_struct_0(esk3_0),X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_40]),c_0_26])])).

cnf(c_0_45,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk3_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_26])])).

cnf(c_0_46,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk3_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_48,plain,
    ( ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X3),X2)
    | ~ v1_subset_1(k2_struct_0(X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_struct_0(X3)
    | ~ r1_tarski(u1_struct_0(X3),X1)
    | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_14]),c_0_18])])).

cnf(c_0_51,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | ~ v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(esk3_0))
    | ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(esk3_0)))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_26])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_subset_1(k2_struct_0(esk3_0),X1)
    | ~ l1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_18])]),c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_subset_1(k2_struct_0(esk3_0),k2_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | v1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ v1_subset_1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( v1_subset_1(X1,u1_struct_0(esk3_0))
    | v1_subset_1(esk4_0,X1)
    | ~ v3_tex_2(X1,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_14]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_subset_1(k2_struct_0(esk3_0),X1)
    | ~ r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_14]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_tex_2(k2_struct_0(esk3_0),X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v1_subset_1(X2,X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_struct_0(esk3_0))
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | ~ v1_subset_1(esk4_0,k2_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( v1_subset_1(esk4_0,k2_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_58]),c_0_38]),c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_subset_1(k2_struct_0(esk3_0),esk4_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_tex_2(k2_struct_0(esk3_0),esk3_0)
    | ~ v3_tex_2(X1,esk3_0)
    | ~ v1_subset_1(X1,X1)
    | ~ r1_tarski(X1,k2_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_26]),c_0_18])])).

cnf(c_0_66,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_67,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_subset_1(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( v1_subset_1(k2_struct_0(esk3_0),X1)
    | ~ v1_subset_1(X1,esk4_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_27])).

fof(c_0_70,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v3_tex_2(X1,esk3_0)
    | ~ v1_subset_1(X1,X1)
    | ~ r1_tarski(X1,k2_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_38]),c_0_18]),c_0_26])])).

cnf(c_0_72,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_14]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk3_0),esk4_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_26])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),X1)
    | v1_subset_1(esk4_0,X1)
    | ~ v3_tex_2(esk4_0,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_subset_1(esk4_0,esk4_0)
    | ~ r1_tarski(esk4_0,k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_42]),c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk3_0),esk4_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_49])])).

cnf(c_0_78,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),X1)
    | v1_subset_1(esk4_0,X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_72])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_subset_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_59])])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_42]),c_0_72]),c_0_18])]),c_0_29])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_74]),c_0_49])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_74]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:47:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.38/0.56  # and selection function PSelectUnlessUniqMaxPos.
% 0.38/0.56  #
% 0.38/0.56  # Preprocessing time       : 0.021 s
% 0.38/0.56  # Presaturation interreduction done
% 0.38/0.56  
% 0.38/0.56  # Proof found!
% 0.38/0.56  # SZS status Theorem
% 0.38/0.56  # SZS output start CNFRefutation
% 0.38/0.56  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.38/0.56  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.38/0.56  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 0.38/0.56  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 0.38/0.56  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.38/0.56  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 0.38/0.56  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.38/0.56  fof(fc12_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_tops_1(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_tops_1)).
% 0.38/0.56  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.38/0.56  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.56  fof(c_0_10, plain, ![X17]:(~l1_struct_0(X17)|m1_subset_1(k2_struct_0(X17),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.38/0.56  fof(c_0_11, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.38/0.56  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.38/0.56  cnf(c_0_13, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.38/0.56  cnf(c_0_14, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.56  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v1_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_tex_2(esk4_0,esk3_0)|v1_subset_1(esk4_0,u1_struct_0(esk3_0)))&(v3_tex_2(esk4_0,esk3_0)|~v1_subset_1(esk4_0,u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.38/0.56  fof(c_0_16, plain, ![X46, X47]:(v2_struct_0(X46)|~v2_pre_topc(X46)|~v1_tdlat_3(X46)|~l1_pre_topc(X46)|(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|v2_tex_2(X47,X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.38/0.56  cnf(c_0_17, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.38/0.56  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  fof(c_0_19, plain, ![X37, X38]:((~v1_subset_1(X38,X37)|X38!=X37|~m1_subset_1(X38,k1_zfmisc_1(X37)))&(X38=X37|v1_subset_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.38/0.56  fof(c_0_20, plain, ![X48, X49]:(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(~v1_tops_1(X49,X48)|~v2_tex_2(X49,X48)|v3_tex_2(X49,X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 0.38/0.56  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.38/0.56  cnf(c_0_23, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  fof(c_0_25, plain, ![X19]:(~l1_struct_0(X19)|~v1_subset_1(k2_struct_0(X19),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.38/0.56  cnf(c_0_26, negated_conjecture, (m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.38/0.56  cnf(c_0_27, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.56  cnf(c_0_28, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.56  cnf(c_0_29, negated_conjecture, (v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_18])])).
% 0.38/0.56  cnf(c_0_30, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.56  cnf(c_0_31, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk3_0))|m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.38/0.56  cnf(c_0_32, negated_conjecture, (v3_tex_2(X1,esk3_0)|~v1_tops_1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_28]), c_0_24]), c_0_18])]), c_0_29])).
% 0.38/0.56  fof(c_0_33, plain, ![X31]:(~l1_pre_topc(X31)|v1_tops_1(k2_struct_0(X31),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc12_tops_1])])).
% 0.38/0.56  cnf(c_0_34, negated_conjecture, (m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(k2_struct_0(esk3_0)))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26])])).
% 0.38/0.56  cnf(c_0_35, negated_conjecture, (v3_tex_2(k2_struct_0(esk3_0),esk3_0)|~v1_tops_1(k2_struct_0(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.38/0.56  cnf(c_0_36, plain, (v1_tops_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.56  cnf(c_0_37, negated_conjecture, (m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(k2_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_38, negated_conjecture, (v3_tex_2(k2_struct_0(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_18])])).
% 0.38/0.56  fof(c_0_39, plain, ![X39, X40, X41]:(((v2_tex_2(X40,X39)|~v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|(~v2_tex_2(X41,X39)|~r1_tarski(X40,X41)|X40=X41)|~v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39)))&((m1_subset_1(esk1_2(X39,X40),k1_zfmisc_1(u1_struct_0(X39)))|~v2_tex_2(X40,X39)|v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(((v2_tex_2(esk1_2(X39,X40),X39)|~v2_tex_2(X40,X39)|v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(r1_tarski(X40,esk1_2(X39,X40))|~v2_tex_2(X40,X39)|v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39)))&(X40!=esk1_2(X39,X40)|~v2_tex_2(X40,X39)|v3_tex_2(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.38/0.56  cnf(c_0_40, negated_conjecture, (v1_subset_1(k2_struct_0(esk3_0),X1)|m1_subset_1(X1,k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.38/0.56  cnf(c_0_41, negated_conjecture, (v3_tex_2(X1,esk3_0)|v1_subset_1(k2_struct_0(esk3_0),X1)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_27])).
% 0.38/0.56  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  cnf(c_0_43, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.56  cnf(c_0_44, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_40]), c_0_26])])).
% 0.38/0.56  cnf(c_0_45, negated_conjecture, (v3_tex_2(u1_struct_0(esk3_0),esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_41]), c_0_26])])).
% 0.38/0.56  cnf(c_0_46, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.56  cnf(c_0_47, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk3_0))|m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.38/0.56  cnf(c_0_48, plain, (~v2_tex_2(X1,X2)|~v3_tex_2(u1_struct_0(X3),X2)|~v1_subset_1(k2_struct_0(X3),X1)|~l1_pre_topc(X2)|~l1_struct_0(X3)|~r1_tarski(u1_struct_0(X3),X1)|~m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_30, c_0_43])).
% 0.38/0.56  cnf(c_0_49, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_50, negated_conjecture, (v3_tex_2(u1_struct_0(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_51, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_46])).
% 0.38/0.56  cnf(c_0_52, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|~v1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  cnf(c_0_53, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(esk3_0))|~v3_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.56  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(esk3_0)))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_26])])).
% 0.38/0.56  cnf(c_0_55, negated_conjecture, (~v1_subset_1(k2_struct_0(esk3_0),X1)|~l1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_18])]), c_0_29])).
% 0.38/0.56  cnf(c_0_56, negated_conjecture, (~v1_subset_1(k2_struct_0(esk3_0),k2_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 0.38/0.56  cnf(c_0_57, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|v1_subset_1(X1,u1_struct_0(esk3_0))|~v1_subset_1(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_52, c_0_27])).
% 0.38/0.56  cnf(c_0_58, negated_conjecture, (v1_subset_1(X1,u1_struct_0(esk3_0))|v1_subset_1(esk4_0,X1)|~v3_tex_2(X1,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 0.38/0.56  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_60, negated_conjecture, (~v1_subset_1(k2_struct_0(esk3_0),X1)|~r1_tarski(u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_61, negated_conjecture, (~v2_tex_2(k2_struct_0(esk3_0),X1)|~v3_tex_2(X2,X1)|~v1_subset_1(X2,X2)|~l1_pre_topc(X1)|~r1_tarski(X2,k2_struct_0(esk3_0))|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_43])).
% 0.38/0.56  cnf(c_0_62, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|~v1_subset_1(esk4_0,k2_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_57]), c_0_26])])).
% 0.38/0.56  cnf(c_0_63, negated_conjecture, (v1_subset_1(esk4_0,k2_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_58]), c_0_38]), c_0_59])])).
% 0.38/0.56  cnf(c_0_64, negated_conjecture, (~v1_subset_1(k2_struct_0(esk3_0),esk4_0)|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_42])).
% 0.38/0.56  cnf(c_0_65, negated_conjecture, (~v2_tex_2(k2_struct_0(esk3_0),esk3_0)|~v3_tex_2(X1,esk3_0)|~v1_subset_1(X1,X1)|~r1_tarski(X1,k2_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_26]), c_0_18])])).
% 0.38/0.56  cnf(c_0_66, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.56  cnf(c_0_67, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.38/0.56  cnf(c_0_68, negated_conjecture, (~v1_subset_1(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_49])).
% 0.38/0.56  cnf(c_0_69, negated_conjecture, (v1_subset_1(k2_struct_0(esk3_0),X1)|~v1_subset_1(X1,esk4_0)|~r1_tarski(u1_struct_0(esk3_0),esk4_0)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_27])).
% 0.38/0.56  fof(c_0_70, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.56  cnf(c_0_71, negated_conjecture, (~v3_tex_2(X1,esk3_0)|~v1_subset_1(X1,X1)|~r1_tarski(X1,k2_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_38]), c_0_18]), c_0_26])])).
% 0.38/0.56  cnf(c_0_72, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_14]), c_0_18])])).
% 0.38/0.56  cnf(c_0_73, negated_conjecture, (~v1_subset_1(u1_struct_0(esk3_0),esk4_0)|~r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_26])])).
% 0.38/0.56  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.38/0.56  cnf(c_0_75, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),X1)|v1_subset_1(esk4_0,X1)|~v3_tex_2(esk4_0,esk3_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 0.38/0.56  cnf(c_0_76, negated_conjecture, (~v1_subset_1(esk4_0,esk4_0)|~r1_tarski(esk4_0,k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_42]), c_0_72])])).
% 0.38/0.56  cnf(c_0_77, negated_conjecture, (~v1_subset_1(u1_struct_0(esk3_0),esk4_0)|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_49])])).
% 0.38/0.56  cnf(c_0_78, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),X1)|v1_subset_1(esk4_0,X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_72])])).
% 0.38/0.56  cnf(c_0_79, negated_conjecture, (~v1_subset_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_74]), c_0_59])])).
% 0.38/0.56  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.38/0.56  cnf(c_0_81, negated_conjecture, (~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80])).
% 0.38/0.56  cnf(c_0_82, negated_conjecture, (~v2_tex_2(X1,X2)|~v3_tex_2(esk4_0,X2)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(esk3_0),X1)|~r1_tarski(esk4_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_81, c_0_43])).
% 0.38/0.56  cnf(c_0_83, negated_conjecture, (~r1_tarski(u1_struct_0(esk3_0),X1)|~r1_tarski(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_42]), c_0_72]), c_0_18])]), c_0_29])).
% 0.38/0.56  cnf(c_0_84, negated_conjecture, (~r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_49])).
% 0.38/0.56  cnf(c_0_85, negated_conjecture, (~r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_74]), c_0_49])])).
% 0.38/0.56  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_74]), c_0_42])]), ['proof']).
% 0.38/0.56  # SZS output end CNFRefutation
% 0.38/0.56  # Proof object total steps             : 87
% 0.38/0.56  # Proof object clause steps            : 66
% 0.38/0.56  # Proof object formula steps           : 21
% 0.38/0.56  # Proof object conjectures             : 54
% 0.38/0.56  # Proof object clause conjectures      : 51
% 0.38/0.56  # Proof object formula conjectures     : 3
% 0.38/0.56  # Proof object initial clauses used    : 19
% 0.38/0.56  # Proof object initial formulas used   : 10
% 0.38/0.56  # Proof object generating inferences   : 45
% 0.38/0.56  # Proof object simplifying inferences  : 66
% 0.38/0.56  # Training examples: 0 positive, 0 negative
% 0.38/0.56  # Parsed axioms                        : 22
% 0.38/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.56  # Initial clauses                      : 42
% 0.38/0.56  # Removed in clause preprocessing      : 0
% 0.38/0.56  # Initial clauses in saturation        : 42
% 0.38/0.56  # Processed clauses                    : 1651
% 0.38/0.56  # ...of these trivial                  : 3
% 0.38/0.56  # ...subsumed                          : 874
% 0.38/0.56  # ...remaining for further processing  : 774
% 0.38/0.56  # Other redundant clauses eliminated   : 141
% 0.38/0.56  # Clauses deleted for lack of memory   : 0
% 0.38/0.56  # Backward-subsumed                    : 86
% 0.38/0.56  # Backward-rewritten                   : 27
% 0.38/0.56  # Generated clauses                    : 10567
% 0.38/0.56  # ...of the previous two non-trivial   : 9751
% 0.38/0.56  # Contextual simplify-reflections      : 20
% 0.38/0.56  # Paramodulations                      : 10300
% 0.38/0.56  # Factorizations                       : 126
% 0.38/0.56  # Equation resolutions                 : 141
% 0.38/0.56  # Propositional unsat checks           : 0
% 0.38/0.56  #    Propositional check models        : 0
% 0.38/0.56  #    Propositional check unsatisfiable : 0
% 0.38/0.56  #    Propositional clauses             : 0
% 0.38/0.56  #    Propositional clauses after purity: 0
% 0.38/0.56  #    Propositional unsat core size     : 0
% 0.38/0.56  #    Propositional preprocessing time  : 0.000
% 0.38/0.56  #    Propositional encoding time       : 0.000
% 0.38/0.56  #    Propositional solver time         : 0.000
% 0.38/0.56  #    Success case prop preproc time    : 0.000
% 0.38/0.56  #    Success case prop encoding time   : 0.000
% 0.38/0.56  #    Success case prop solver time     : 0.000
% 0.38/0.56  # Current number of processed clauses  : 618
% 0.38/0.56  #    Positive orientable unit clauses  : 14
% 0.38/0.56  #    Positive unorientable unit clauses: 0
% 0.38/0.56  #    Negative unit clauses             : 9
% 0.38/0.56  #    Non-unit-clauses                  : 595
% 0.38/0.56  # Current number of unprocessed clauses: 7768
% 0.38/0.56  # ...number of literals in the above   : 65197
% 0.38/0.56  # Current number of archived formulas  : 0
% 0.38/0.56  # Current number of archived clauses   : 155
% 0.38/0.56  # Clause-clause subsumption calls (NU) : 101237
% 0.38/0.56  # Rec. Clause-clause subsumption calls : 17315
% 0.38/0.56  # Non-unit clause-clause subsumptions  : 727
% 0.38/0.56  # Unit Clause-clause subsumption calls : 1613
% 0.38/0.56  # Rewrite failures with RHS unbound    : 0
% 0.38/0.56  # BW rewrite match attempts            : 9
% 0.38/0.56  # BW rewrite match successes           : 9
% 0.38/0.56  # Condensation attempts                : 0
% 0.38/0.56  # Condensation successes               : 0
% 0.38/0.56  # Termbank termtop insertions          : 223719
% 0.38/0.56  
% 0.38/0.56  # -------------------------------------------------
% 0.38/0.56  # User time                : 0.209 s
% 0.38/0.56  # System time              : 0.009 s
% 0.38/0.56  # Total time               : 0.218 s
% 0.38/0.56  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
