%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 406 expanded)
%              Number of clauses        :   48 ( 161 expanded)
%              Number of leaves         :   14 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  251 (1773 expanded)
%              Number of equality atoms :   36 ( 116 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(t27_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ v1_subset_1(X16,X15)
        | X16 != X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( X16 = X15
        | v1_subset_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v1_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_tex_2(esk3_0,esk2_0)
      | v1_subset_1(esk3_0,u1_struct_0(esk2_0)) )
    & ( v3_tex_2(esk3_0,esk2_0)
      | ~ v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k2_struct_0(X9) = u1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ( v2_tex_2(X18,X17)
        | ~ v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X19,X17)
        | ~ r1_tarski(X18,X19)
        | X18 = X19
        | ~ v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk1_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( v2_tex_2(esk1_2(X17,X18),X17)
        | ~ v2_tex_2(X18,X17)
        | v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(X18,esk1_2(X17,X18))
        | ~ v2_tex_2(X18,X17)
        | v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( X18 != esk1_2(X17,X18)
        | ~ v2_tex_2(X18,X17)
        | v3_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_21,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_22,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ v1_tdlat_3(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | v2_tex_2(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

fof(c_0_25,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | ~ v1_tdlat_3(X12)
      | v2_pre_topc(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ v1_tops_1(X24,X23)
      | ~ v2_tex_2(X24,X23)
      | v3_tex_2(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

fof(c_0_38,plain,(
    ! [X13,X14] :
      ( ( ~ v1_tops_1(X14,X13)
        | k2_pre_topc(X13,X14) = u1_struct_0(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( k2_pre_topc(X13,X14) != u1_struct_0(X13)
        | v1_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_39,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,k2_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk3_0
    | ~ v2_tex_2(X1,esk2_0)
    | ~ v3_tex_2(esk3_0,esk2_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_30])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_46,plain,(
    ! [X6] : ~ v1_subset_1(k2_subset_1(X6),X6) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_subset_1(esk3_0,k2_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ v2_tex_2(u1_struct_0(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(u1_struct_0(X1),X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_56,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ v2_tex_2(esk3_0,esk2_0)
    | ~ v1_tops_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_18]),c_0_48]),c_0_30])]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( v2_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_50]),c_0_30])]),c_0_49])).

cnf(c_0_59,plain,
    ( v1_tops_1(X1,X2)
    | k2_pre_topc(X2,X1) != k2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(esk2_0))
    | ~ v3_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_50]),c_0_30])]),c_0_49])).

cnf(c_0_64,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ v1_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( v1_tops_1(esk3_0,esk2_0)
    | k2_pre_topc(esk2_0,esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_30])])).

cnf(c_0_67,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_30])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v3_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

fof(c_0_69,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | k2_pre_topc(X11,k2_struct_0(X11)) = k2_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).

cnf(c_0_70,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | k2_pre_topc(esk2_0,esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) != esk3_0
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_30])])).

cnf(c_0_75,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_40]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:29:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.19/0.38  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 0.19/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.19/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 0.19/0.38  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 0.19/0.38  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.19/0.38  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.19/0.38  fof(t27_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 0.19/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.19/0.38  fof(c_0_15, plain, ![X15, X16]:((~v1_subset_1(X16,X15)|X16!=X15|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(X16=X15|v1_subset_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v1_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_tex_2(esk3_0,esk2_0)|v1_subset_1(esk3_0,u1_struct_0(esk2_0)))&(v3_tex_2(esk3_0,esk2_0)|~v1_subset_1(esk3_0,u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_19, plain, ![X9]:(~l1_struct_0(X9)|k2_struct_0(X9)=u1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  fof(c_0_20, plain, ![X17, X18, X19]:(((v2_tex_2(X18,X17)|~v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_tex_2(X19,X17)|~r1_tarski(X18,X19)|X18=X19)|~v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17)))&((m1_subset_1(esk1_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|~v2_tex_2(X18,X17)|v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(((v2_tex_2(esk1_2(X17,X18),X17)|~v2_tex_2(X18,X17)|v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(r1_tarski(X18,esk1_2(X17,X18))|~v2_tex_2(X18,X17)|v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17)))&(X18!=esk1_2(X17,X18)|~v2_tex_2(X18,X17)|v3_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.19/0.38  fof(c_0_21, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.38  fof(c_0_22, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.38  fof(c_0_23, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  fof(c_0_24, plain, ![X21, X22]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~v1_tdlat_3(X21)|~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v2_tex_2(X22,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X12]:(~l1_pre_topc(X12)|(~v1_tdlat_3(X12)|v2_pre_topc(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_28, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_29, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_31, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_32, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_36, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_37, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~v1_tops_1(X24,X23)|~v2_tex_2(X24,X23)|v3_tex_2(X24,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 0.19/0.38  fof(c_0_38, plain, ![X13, X14]:((~v1_tops_1(X14,X13)|k2_pre_topc(X13,X14)=u1_struct_0(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(k2_pre_topc(X13,X14)!=u1_struct_0(X13)|v1_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,k2_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_40, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (X1=esk3_0|~v2_tex_2(X1,esk2_0)|~v3_tex_2(esk3_0,esk2_0)|~r1_tarski(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_30])])).
% 0.19/0.38  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_18])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.19/0.38  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  fof(c_0_46, plain, ![X6]:~v1_subset_1(k2_subset_1(X6),X6), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.19/0.38  cnf(c_0_47, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v1_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~l1_struct_0(esk2_0)|~v1_subset_1(esk3_0,k2_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_30])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~v2_tex_2(u1_struct_0(esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_44])).
% 0.19/0.38  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_tex_2(u1_struct_0(X1),X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 0.19/0.38  cnf(c_0_56, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~v2_tex_2(esk3_0,esk2_0)|~v1_tops_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_18]), c_0_48]), c_0_30])]), c_0_49])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (v2_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_18]), c_0_50]), c_0_30])]), c_0_49])).
% 0.19/0.38  cnf(c_0_59, plain, (v1_tops_1(X1,X2)|k2_pre_topc(X2,X1)!=k2_struct_0(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_40])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_27])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(esk2_0))|~v3_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_50]), c_0_30])]), c_0_49])).
% 0.19/0.38  cnf(c_0_64, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_56, c_0_32])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~v1_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (v1_tops_1(esk3_0,esk2_0)|k2_pre_topc(esk2_0,esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_30])])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_40]), c_0_30])])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (~v3_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.38  fof(c_0_69, plain, ![X11]:(~l1_pre_topc(X11)|k2_pre_topc(X11,k2_struct_0(X11))=k2_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|k2_pre_topc(esk2_0,esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0), inference(sr,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.38  cnf(c_0_72, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)!=esk3_0|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_68])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_71]), c_0_30])])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_40]), c_0_30])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 77
% 0.19/0.38  # Proof object clause steps            : 48
% 0.19/0.38  # Proof object formula steps           : 29
% 0.19/0.38  # Proof object conjectures             : 33
% 0.19/0.38  # Proof object clause conjectures      : 30
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 14
% 0.19/0.38  # Proof object generating inferences   : 20
% 0.19/0.38  # Proof object simplifying inferences  : 40
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 14
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 146
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 23
% 0.19/0.38  # ...remaining for further processing  : 123
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 7
% 0.19/0.38  # Backward-rewritten                   : 38
% 0.19/0.38  # Generated clauses                    : 174
% 0.19/0.38  # ...of the previous two non-trivial   : 183
% 0.19/0.38  # Contextual simplify-reflections      : 9
% 0.19/0.38  # Paramodulations                      : 163
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 41
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 27
% 0.19/0.38  # Current number of unprocessed clauses: 89
% 0.19/0.38  # ...number of literals in the above   : 358
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 82
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1194
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 500
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 34
% 0.19/0.38  # Unit Clause-clause subsumption calls : 44
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 8
% 0.19/0.38  # BW rewrite match successes           : 4
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5097
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
