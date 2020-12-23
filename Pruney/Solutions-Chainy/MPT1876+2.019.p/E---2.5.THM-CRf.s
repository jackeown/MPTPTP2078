%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 569 expanded)
%              Number of clauses        :   52 ( 192 expanded)
%              Number of leaves         :   16 ( 142 expanded)
%              Depth                    :   10
%              Number of atoms          :  335 (3842 expanded)
%              Number of equality atoms :   12 (  49 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(cc32_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2) )
           => ( ~ v2_struct_0(X2)
              & ~ v1_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

fof(c_0_17,plain,(
    ! [X36,X37] :
      ( ( ~ v2_struct_0(X37)
        | v2_struct_0(X37)
        | v7_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ v2_tdlat_3(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ v1_tdlat_3(X37)
        | v2_struct_0(X37)
        | v7_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ v2_tdlat_3(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | ~ v2_tdlat_3(X35)
      | v2_pre_topc(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( v1_xboole_0(X38)
      | v1_xboole_0(X39)
      | ~ v1_zfmisc_1(X39)
      | ~ r1_tarski(X38,X39)
      | X38 = X39 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ( ~ r1_tarski(k1_tarski(X21),X22)
        | r2_hidden(X21,X22) )
      & ( ~ r2_hidden(X21,X22)
        | r1_tarski(k1_tarski(X21),X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_21,plain,(
    ! [X20] : ~ v1_xboole_0(k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X40,X41] :
      ( ( ~ v2_struct_0(esk3_2(X40,X41))
        | ~ v2_tex_2(X41,X40)
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_pre_topc(esk3_2(X40,X41))
        | ~ v2_tex_2(X41,X40)
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_tdlat_3(esk3_2(X40,X41))
        | ~ v2_tex_2(X41,X40)
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_pre_topc(esk3_2(X40,X41),X40)
        | ~ v2_tex_2(X41,X40)
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( X41 = u1_struct_0(esk3_2(X40,X41))
        | ~ v2_tex_2(X41,X40)
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v2_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v2_tex_2(esk5_0,esk4_0)
      | ~ v1_zfmisc_1(esk5_0) )
    & ( v2_tex_2(esk5_0,esk4_0)
      | v1_zfmisc_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X32] :
      ( ~ v7_struct_0(X32)
      | ~ l1_struct_0(X32)
      | v1_zfmisc_1(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_32,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk3_2(esk4_0,esk5_0)) = esk5_0
    | ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,plain,
    ( v2_struct_0(esk3_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( v2_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( v1_tdlat_3(esk3_2(esk4_0,esk5_0))
    | ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v2_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37])).

fof(c_0_52,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( v1_zfmisc_1(esk5_0)
    | ~ v7_struct_0(esk3_2(esk4_0,esk5_0))
    | ~ l1_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v7_struct_0(esk3_2(esk4_0,esk5_0))
    | ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_49]),c_0_35])]),c_0_36]),c_0_37]),c_0_50]),c_0_51])).

fof(c_0_58,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_59,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X43,X44] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | v2_tex_2(k6_domain_1(u1_struct_0(X43),X44),X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_62,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),X2)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( v1_zfmisc_1(esk5_0)
    | ~ l1_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_47])).

cnf(c_0_66,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_37])).

cnf(c_0_72,negated_conjecture,
    ( v1_zfmisc_1(esk5_0)
    | ~ l1_pre_topc(esk3_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk3_2(esk4_0,esk5_0))
    | ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37])).

fof(c_0_74,plain,(
    ! [X23,X24] :
      ( ~ v1_xboole_0(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_75,plain,
    ( v2_tex_2(k1_tarski(X1),X2)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( v1_zfmisc_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | v1_xboole_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk1_1(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_54])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_33]),c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_34]),c_0_77]),c_0_35])]),c_0_82]),c_0_36]),c_0_83]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:48:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.028 s
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 0.19/0.44  fof(cc32_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v7_struct_0(X2)))=>(~(v2_struct_0(X2))&~(v1_tdlat_3(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 0.19/0.44  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.19/0.44  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.44  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.44  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.19/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.44  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 0.19/0.44  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.19/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.44  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.19/0.44  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.44  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.44  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.44  fof(c_0_16, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.19/0.44  fof(c_0_17, plain, ![X36, X37]:((~v2_struct_0(X37)|(v2_struct_0(X37)|v7_struct_0(X37))|~m1_pre_topc(X37,X36)|(v2_struct_0(X36)|~v2_pre_topc(X36)|~v2_tdlat_3(X36)|~l1_pre_topc(X36)))&(~v1_tdlat_3(X37)|(v2_struct_0(X37)|v7_struct_0(X37))|~m1_pre_topc(X37,X36)|(v2_struct_0(X36)|~v2_pre_topc(X36)|~v2_tdlat_3(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).
% 0.19/0.44  fof(c_0_18, plain, ![X35]:(~l1_pre_topc(X35)|(~v2_tdlat_3(X35)|v2_pre_topc(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.19/0.44  fof(c_0_19, plain, ![X38, X39]:(v1_xboole_0(X38)|(v1_xboole_0(X39)|~v1_zfmisc_1(X39)|(~r1_tarski(X38,X39)|X38=X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.19/0.44  fof(c_0_20, plain, ![X21, X22]:((~r1_tarski(k1_tarski(X21),X22)|r2_hidden(X21,X22))&(~r2_hidden(X21,X22)|r1_tarski(k1_tarski(X21),X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.44  fof(c_0_21, plain, ![X20]:~v1_xboole_0(k1_tarski(X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.19/0.44  fof(c_0_22, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.44  fof(c_0_23, plain, ![X40, X41]:(((((~v2_struct_0(esk3_2(X40,X41))|~v2_tex_2(X41,X40)|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(v1_pre_topc(esk3_2(X40,X41))|~v2_tex_2(X41,X40)|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(v1_tdlat_3(esk3_2(X40,X41))|~v2_tex_2(X41,X40)|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(m1_pre_topc(esk3_2(X40,X41),X40)|~v2_tex_2(X41,X40)|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(X41=u1_struct_0(esk3_2(X40,X41))|~v2_tex_2(X41,X40)|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.19/0.44  fof(c_0_24, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v2_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0))&(v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.44  cnf(c_0_25, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v2_struct_0(X2)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_26, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_27, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_28, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_29, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  fof(c_0_31, plain, ![X32]:(~v7_struct_0(X32)|~l1_struct_0(X32)|v1_zfmisc_1(u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.19/0.44  cnf(c_0_32, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.44  cnf(c_0_39, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_40, plain, (v1_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_41, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_42, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.19/0.44  cnf(c_0_43, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  fof(c_0_44, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.44  cnf(c_0_45, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk3_2(esk4_0,esk5_0))=esk5_0|~v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_37])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_48, plain, (v2_struct_0(esk3_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (v2_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (v1_tdlat_3(esk3_2(esk4_0,esk5_0))|~v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_37])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)|~v2_struct_0(esk3_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_37])).
% 0.19/0.44  fof(c_0_52, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.44  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_54, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.44  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (v1_zfmisc_1(esk5_0)|~v7_struct_0(esk3_2(esk4_0,esk5_0))|~l1_struct_0(esk3_2(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (v7_struct_0(esk3_2(esk4_0,esk5_0))|~v2_tex_2(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_49]), c_0_35])]), c_0_36]), c_0_37]), c_0_50]), c_0_51])).
% 0.19/0.44  fof(c_0_58, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.44  cnf(c_0_59, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.44  fof(c_0_60, plain, ![X43, X44]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(~m1_subset_1(X44,u1_struct_0(X43))|v2_tex_2(k6_domain_1(u1_struct_0(X43),X44),X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.19/0.44  fof(c_0_61, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.44  fof(c_0_62, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.44  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),X2)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (v1_zfmisc_1(esk5_0)|~l1_struct_0(esk3_2(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_47])).
% 0.19/0.44  cnf(c_0_66, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.44  cnf(c_0_67, plain, (v2_struct_0(X1)|l1_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_59, c_0_39])).
% 0.19/0.44  cnf(c_0_68, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.44  cnf(c_0_69, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.44  cnf(c_0_70, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.44  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0))|~v1_zfmisc_1(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_37])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (v1_zfmisc_1(esk5_0)|~l1_pre_topc(esk3_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (l1_pre_topc(esk3_2(esk4_0,esk5_0))|~v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_37])).
% 0.19/0.44  fof(c_0_74, plain, ![X23, X24]:(~v1_xboole_0(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_xboole_0(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.44  cnf(c_0_75, plain, (v2_tex_2(k1_tarski(X1),X2)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))|~v1_zfmisc_1(esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (v1_zfmisc_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_47])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_79, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.44  cnf(c_0_80, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X2))|v1_xboole_0(X1)|~v2_pre_topc(X2)|~v1_zfmisc_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(esk1_1(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_75, c_0_54])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_77])])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_33]), c_0_37])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_34]), c_0_77]), c_0_35])]), c_0_82]), c_0_36]), c_0_83]), c_0_37]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 85
% 0.19/0.44  # Proof object clause steps            : 52
% 0.19/0.44  # Proof object formula steps           : 33
% 0.19/0.44  # Proof object conjectures             : 27
% 0.19/0.44  # Proof object clause conjectures      : 24
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 28
% 0.19/0.44  # Proof object initial formulas used   : 16
% 0.19/0.44  # Proof object generating inferences   : 21
% 0.19/0.44  # Proof object simplifying inferences  : 48
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 18
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 38
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 37
% 0.19/0.44  # Processed clauses                    : 842
% 0.19/0.44  # ...of these trivial                  : 2
% 0.19/0.44  # ...subsumed                          : 543
% 0.19/0.44  # ...remaining for further processing  : 297
% 0.19/0.44  # Other redundant clauses eliminated   : 3
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 6
% 0.19/0.44  # Backward-rewritten                   : 26
% 0.19/0.44  # Generated clauses                    : 3400
% 0.19/0.44  # ...of the previous two non-trivial   : 3025
% 0.19/0.44  # Contextual simplify-reflections      : 16
% 0.19/0.44  # Paramodulations                      : 3377
% 0.19/0.44  # Factorizations                       : 20
% 0.19/0.44  # Equation resolutions                 : 3
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 262
% 0.19/0.44  #    Positive orientable unit clauses  : 14
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 5
% 0.19/0.44  #    Non-unit-clauses                  : 243
% 0.19/0.44  # Current number of unprocessed clauses: 2198
% 0.19/0.44  # ...number of literals in the above   : 9640
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 32
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 10029
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 5360
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 490
% 0.19/0.44  # Unit Clause-clause subsumption calls : 41
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 2
% 0.19/0.44  # BW rewrite match successes           : 2
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 54085
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.101 s
% 0.19/0.44  # System time              : 0.008 s
% 0.19/0.44  # Total time               : 0.109 s
% 0.19/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
