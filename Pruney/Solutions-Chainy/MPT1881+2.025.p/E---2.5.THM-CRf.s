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
% DateTime   : Thu Dec  3 11:20:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 446 expanded)
%              Number of clauses        :   48 ( 177 expanded)
%              Number of leaves         :   15 ( 111 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 (1888 expanded)
%              Number of equality atoms :   33 ( 127 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(t27_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X16,X17] :
      ( ( ~ v1_subset_1(X17,X16)
        | X17 != X16
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( X17 = X16
        | v1_subset_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v1_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_tex_2(esk3_0,esk2_0)
      | v1_subset_1(esk3_0,u1_struct_0(esk2_0)) )
    & ( v3_tex_2(esk3_0,esk2_0)
      | ~ v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_struct_0(X9),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_19,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | ~ v1_subset_1(k2_struct_0(X11),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( v2_tex_2(X19,X18)
        | ~ v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X20,X18)
        | ~ r1_tarski(X19,X20)
        | X19 = X20
        | ~ v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk1_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( v2_tex_2(esk1_2(X18,X19),X18)
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(X19,esk1_2(X18,X19))
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( X19 != esk1_2(X18,X19)
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_25,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_26,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ v1_tdlat_3(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | v2_tex_2(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

fof(c_0_29,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | ~ v1_tdlat_3(X13)
      | v2_pre_topc(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( u1_struct_0(X1) = k2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_22]),c_0_23])).

fof(c_0_32,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_33,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,k2_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk3_0
    | ~ v2_tex_2(X1,esk2_0)
    | ~ v3_tex_2(esk3_0,esk2_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_34])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X6] : ~ v1_subset_1(k2_subset_1(X6),X6) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_49,plain,(
    ! [X14,X15] :
      ( ( ~ v1_tops_1(X15,X14)
        | k2_pre_topc(X14,X15) = u1_struct_0(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( k2_pre_topc(X14,X15) != u1_struct_0(X14)
        | v1_tops_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_50,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_subset_1(esk3_0,k2_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v1_subset_1(esk3_0,k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ v2_tex_2(u1_struct_0(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(u1_struct_0(X1),X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v1_tops_1(X25,X24)
      | ~ v2_tex_2(X25,X24)
      | v3_tex_2(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

cnf(c_0_58,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(esk2_0))
    | ~ v3_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_34])]),c_0_55])).

cnf(c_0_62,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_36])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v2_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_54]),c_0_34])]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,plain,
    ( v1_tops_1(X1,X2)
    | k2_pre_topc(X2,X1) != k2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

fof(c_0_68,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | k2_pre_topc(X12,k2_struct_0(X12)) = k2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0
    | v3_tex_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v3_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | ~ v1_tops_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_21]),c_0_64]),c_0_65]),c_0_34])]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( v1_tops_1(esk3_0,esk2_0)
    | k2_pre_topc(esk2_0,esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34])])).

cnf(c_0_73,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k2_struct_0(esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0)
    | k2_pre_topc(esk2_0,esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_34])])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_74]),c_0_70]),c_0_76])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_42]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.19/0.40  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.040 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 0.19/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.40  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.19/0.40  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.19/0.40  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.19/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 0.19/0.40  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.19/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.40  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.19/0.40  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 0.19/0.40  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 0.19/0.40  fof(t27_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.19/0.40  fof(c_0_16, plain, ![X16, X17]:((~v1_subset_1(X17,X16)|X17!=X16|~m1_subset_1(X17,k1_zfmisc_1(X16)))&(X17=X16|v1_subset_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v1_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_tex_2(esk3_0,esk2_0)|v1_subset_1(esk3_0,u1_struct_0(esk2_0)))&(v3_tex_2(esk3_0,esk2_0)|~v1_subset_1(esk3_0,u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.40  fof(c_0_18, plain, ![X9]:(~l1_struct_0(X9)|m1_subset_1(k2_struct_0(X9),k1_zfmisc_1(u1_struct_0(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.19/0.40  fof(c_0_19, plain, ![X11]:(~l1_struct_0(X11)|~v1_subset_1(k2_struct_0(X11),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.19/0.40  cnf(c_0_20, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_22, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_23, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_24, plain, ![X18, X19, X20]:(((v2_tex_2(X19,X18)|~v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_tex_2(X20,X18)|~r1_tarski(X19,X20)|X19=X20)|~v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18)))&((m1_subset_1(esk1_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(((v2_tex_2(esk1_2(X18,X19),X18)|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(r1_tarski(X19,esk1_2(X18,X19))|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18)))&(X19!=esk1_2(X18,X19)|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.19/0.40  fof(c_0_25, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.40  fof(c_0_26, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.40  fof(c_0_27, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_28, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~v1_tdlat_3(X22)|~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v2_tex_2(X23,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.19/0.40  fof(c_0_29, plain, ![X13]:(~l1_pre_topc(X13)|(~v1_tdlat_3(X13)|v2_pre_topc(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_31, plain, (u1_struct_0(X1)=k2_struct_0(X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_22]), c_0_23])).
% 0.19/0.40  fof(c_0_32, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.40  cnf(c_0_33, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_35, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_36, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_39, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_40, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,k2_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.40  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (X1=esk3_0|~v2_tex_2(X1,esk2_0)|~v3_tex_2(esk3_0,esk2_0)|~r1_tarski(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_34])])).
% 0.19/0.40  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_21])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.19/0.40  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  fof(c_0_48, plain, ![X6]:~v1_subset_1(k2_subset_1(X6),X6), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.19/0.40  fof(c_0_49, plain, ![X14, X15]:((~v1_tops_1(X15,X14)|k2_pre_topc(X14,X15)=u1_struct_0(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(k2_pre_topc(X14,X15)!=u1_struct_0(X14)|v1_tops_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~l1_struct_0(esk2_0)|~v1_subset_1(esk3_0,k2_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v1_subset_1(esk3_0,k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34])])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~v2_tex_2(u1_struct_0(esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), c_0_46])).
% 0.19/0.40  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_tex_2(u1_struct_0(X1),X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (v1_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_56, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  fof(c_0_57, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v1_tops_1(X25,X24)|~v2_tex_2(X25,X24)|v3_tex_2(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 0.19/0.40  cnf(c_0_58, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(esk2_0))|~v3_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_34])]), c_0_55])).
% 0.19/0.40  cnf(c_0_62, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_56, c_0_36])).
% 0.19/0.40  cnf(c_0_63, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (v2_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_54]), c_0_34])]), c_0_55])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_66, plain, (v1_tops_1(X1,X2)|k2_pre_topc(X2,X1)!=k2_struct_0(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_31]), c_0_42])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.19/0.40  fof(c_0_68, plain, ![X12]:(~l1_pre_topc(X12)|k2_pre_topc(X12,k2_struct_0(X12))=k2_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0|v3_tex_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_34])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (~v3_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|~v1_tops_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_21]), c_0_64]), c_0_65]), c_0_34])]), c_0_55])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (v1_tops_1(esk3_0,esk2_0)|k2_pre_topc(esk2_0,esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_34])])).
% 0.19/0.40  cnf(c_0_73, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k2_struct_0(esk2_0)=esk3_0), inference(sr,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)|k2_pre_topc(esk2_0,esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_34])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_74]), c_0_70]), c_0_76])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_42]), c_0_34])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 79
% 0.19/0.40  # Proof object clause steps            : 48
% 0.19/0.40  # Proof object formula steps           : 31
% 0.19/0.40  # Proof object conjectures             : 31
% 0.19/0.40  # Proof object clause conjectures      : 28
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 21
% 0.19/0.40  # Proof object initial formulas used   : 15
% 0.19/0.40  # Proof object generating inferences   : 21
% 0.19/0.40  # Proof object simplifying inferences  : 40
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 15
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 29
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 174
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 40
% 0.19/0.40  # ...remaining for further processing  : 133
% 0.19/0.40  # Other redundant clauses eliminated   : 1
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 6
% 0.19/0.40  # Backward-rewritten                   : 37
% 0.19/0.40  # Generated clauses                    : 221
% 0.19/0.40  # ...of the previous two non-trivial   : 224
% 0.19/0.40  # Contextual simplify-reflections      : 14
% 0.19/0.40  # Paramodulations                      : 212
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 1
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 54
% 0.19/0.40  #    Positive orientable unit clauses  : 9
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 5
% 0.19/0.40  #    Non-unit-clauses                  : 40
% 0.19/0.40  # Current number of unprocessed clauses: 103
% 0.19/0.40  # ...number of literals in the above   : 398
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 79
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1264
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 566
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 52
% 0.19/0.40  # Unit Clause-clause subsumption calls : 51
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 7
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 5805
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.062 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
