%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 300 expanded)
%              Number of clauses        :   50 ( 116 expanded)
%              Number of leaves         :   17 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  355 (1551 expanded)
%              Number of equality atoms :   14 (  39 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_19,negated_conjecture,(
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

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | m1_subset_1(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_23,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v2_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v2_tex_2(esk4_0,esk3_0)
      | ~ v1_zfmisc_1(esk4_0) )
    & ( v2_tex_2(esk4_0,esk3_0)
      | v1_zfmisc_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k6_domain_1(X1,X2),X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ( ~ v2_struct_0(X28)
        | v2_struct_0(X28)
        | v7_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ v2_tdlat_3(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v1_tdlat_3(X28)
        | v2_struct_0(X28)
        | v7_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ v2_tdlat_3(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).

fof(c_0_32,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | ~ v2_tdlat_3(X26)
      | v2_pre_topc(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_36,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | v1_xboole_0(X30)
      | ~ v1_zfmisc_1(X30)
      | ~ r1_tarski(X29,X30)
      | X29 = X30 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_37,plain,
    ( r1_tarski(k6_domain_1(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_29])).

fof(c_0_39,plain,(
    ! [X8] : ~ v1_xboole_0(k1_tarski(X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ( ~ v2_struct_0(esk2_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_pre_topc(esk2_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_tdlat_3(esk2_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_pre_topc(esk2_2(X31,X32),X31)
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( X32 = u1_struct_0(esk2_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_52,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk1_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_45])).

cnf(c_0_55,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_29])).

fof(c_0_56,plain,(
    ! [X21] :
      ( ~ v7_struct_0(X21)
      | ~ l1_struct_0(X21)
      | v1_zfmisc_1(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( v2_struct_0(esk2_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk2_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_41])).

fof(c_0_59,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_60,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_61,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | v2_tex_2(k6_domain_1(u1_struct_0(X34),X35),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( k1_tarski(esk1_1(esk4_0)) = k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_53]),c_0_54])).

cnf(c_0_63,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_64,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk2_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_41])).

cnf(c_0_67,plain,
    ( v1_tdlat_3(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_68,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk4_0)) = esk4_0
    | ~ v1_zfmisc_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk2_2(X1,X2))
    | ~ l1_struct_0(esk2_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0)
    | ~ v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73]),c_0_53])]),c_0_74]),c_0_75])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( v2_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_zfmisc_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_82]),c_0_73]),c_0_34])]),c_0_74]),c_0_83]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.51  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.51  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.19/0.51  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.51  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.51  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.51  fof(cc32_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v7_struct_0(X2)))=>(~(v2_struct_0(X2))&~(v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 0.19/0.51  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.19/0.51  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.51  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.51  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.19/0.51  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.19/0.51  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.51  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.19/0.51  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.51  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.19/0.51  fof(c_0_17, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.51  fof(c_0_18, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.51  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.19/0.51  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_21, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  fof(c_0_22, plain, ![X11, X12]:(~r2_hidden(X11,X12)|m1_subset_1(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.51  fof(c_0_23, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.51  fof(c_0_24, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|k6_domain_1(X24,X25)=k1_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.51  fof(c_0_25, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.51  fof(c_0_26, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v2_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&((~v2_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0))&(v2_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.19/0.51  cnf(c_0_27, plain, (r1_tarski(k6_domain_1(X1,X2),X1)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.51  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  cnf(c_0_30, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  fof(c_0_31, plain, ![X27, X28]:((~v2_struct_0(X28)|(v2_struct_0(X28)|v7_struct_0(X28))|~m1_pre_topc(X28,X27)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~v2_tdlat_3(X27)|~l1_pre_topc(X27)))&(~v1_tdlat_3(X28)|(v2_struct_0(X28)|v7_struct_0(X28))|~m1_pre_topc(X28,X27)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~v2_tdlat_3(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).
% 0.19/0.51  fof(c_0_32, plain, ![X26]:(~l1_pre_topc(X26)|(~v2_tdlat_3(X26)|v2_pre_topc(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.19/0.51  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  fof(c_0_35, plain, ![X9, X10]:(~v1_xboole_0(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.51  fof(c_0_36, plain, ![X29, X30]:(v1_xboole_0(X29)|(v1_xboole_0(X30)|~v1_zfmisc_1(X30)|(~r1_tarski(X29,X30)|X29=X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.19/0.51  cnf(c_0_37, plain, (r1_tarski(k6_domain_1(X1,X2),X1)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.51  cnf(c_0_38, plain, (k6_domain_1(X1,X2)=k1_tarski(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_29])).
% 0.19/0.51  fof(c_0_39, plain, ![X8]:~v1_xboole_0(k1_tarski(X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.19/0.51  cnf(c_0_40, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v2_struct_0(X2)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.51  cnf(c_0_41, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.51  fof(c_0_42, plain, ![X31, X32]:(((((~v2_struct_0(esk2_2(X31,X32))|~v2_tex_2(X32,X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(v1_pre_topc(esk2_2(X31,X32))|~v2_tex_2(X32,X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(v1_tdlat_3(esk2_2(X31,X32))|~v2_tex_2(X32,X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(m1_pre_topc(esk2_2(X31,X32),X31)|~v2_tex_2(X32,X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(X32=u1_struct_0(esk2_2(X31,X32))|~v2_tex_2(X32,X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.19/0.51  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.51  cnf(c_0_44, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_46, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.51  cnf(c_0_47, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_48, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.51  cnf(c_0_49, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.51  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.51  cnf(c_0_51, plain, (m1_pre_topc(esk2_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.51  fof(c_0_52, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk1_1(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.51  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_45])).
% 0.19/0.51  cnf(c_0_55, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_29])).
% 0.19/0.51  fof(c_0_56, plain, ![X21]:(~v7_struct_0(X21)|~l1_struct_0(X21)|v1_zfmisc_1(u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.19/0.51  cnf(c_0_57, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.51  cnf(c_0_58, plain, (v2_struct_0(esk2_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk2_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_41])).
% 0.19/0.51  fof(c_0_59, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.51  cnf(c_0_60, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.51  fof(c_0_61, plain, ![X34, X35]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|v2_tex_2(k6_domain_1(u1_struct_0(X34),X35),X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.19/0.51  cnf(c_0_62, negated_conjecture, (k1_tarski(esk1_1(esk4_0))=k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_53]), c_0_54])).
% 0.19/0.51  cnf(c_0_63, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_44])).
% 0.19/0.51  cnf(c_0_64, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.51  cnf(c_0_65, plain, (X1=u1_struct_0(esk2_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.51  cnf(c_0_66, plain, (v2_struct_0(X1)|v7_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk2_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_41])).
% 0.19/0.51  cnf(c_0_67, plain, (v1_tdlat_3(esk2_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.51  cnf(c_0_68, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.51  cnf(c_0_69, plain, (v2_struct_0(X1)|l1_pre_topc(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.19/0.51  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.51  cnf(c_0_71, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk4_0))=esk4_0|~v1_zfmisc_1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_45])).
% 0.19/0.51  cnf(c_0_72, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_73, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_74, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_75, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_76, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk2_2(X1,X2))|~l1_struct_0(esk2_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.51  cnf(c_0_77, plain, (v2_struct_0(X1)|v7_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41])).
% 0.19/0.51  cnf(c_0_78, plain, (v2_struct_0(X1)|l1_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.51  cnf(c_0_79, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_80, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73]), c_0_53])]), c_0_74]), c_0_75])).
% 0.19/0.51  cnf(c_0_81, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_41])).
% 0.19/0.51  cnf(c_0_82, negated_conjecture, (v2_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_83, negated_conjecture, (~v1_zfmisc_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.19/0.51  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_82]), c_0_73]), c_0_34])]), c_0_74]), c_0_83]), c_0_45]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 85
% 0.19/0.51  # Proof object clause steps            : 50
% 0.19/0.51  # Proof object formula steps           : 35
% 0.19/0.51  # Proof object conjectures             : 19
% 0.19/0.51  # Proof object clause conjectures      : 16
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 28
% 0.19/0.51  # Proof object initial formulas used   : 17
% 0.19/0.51  # Proof object generating inferences   : 20
% 0.19/0.51  # Proof object simplifying inferences  : 29
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 17
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 31
% 0.19/0.51  # Removed in clause preprocessing      : 1
% 0.19/0.51  # Initial clauses in saturation        : 30
% 0.19/0.51  # Processed clauses                    : 1427
% 0.19/0.51  # ...of these trivial                  : 2
% 0.19/0.51  # ...subsumed                          : 945
% 0.19/0.51  # ...remaining for further processing  : 480
% 0.19/0.51  # Other redundant clauses eliminated   : 0
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 9
% 0.19/0.51  # Backward-rewritten                   : 5
% 0.19/0.51  # Generated clauses                    : 4992
% 0.19/0.51  # ...of the previous two non-trivial   : 4760
% 0.19/0.51  # Contextual simplify-reflections      : 69
% 0.19/0.51  # Paramodulations                      : 4992
% 0.19/0.51  # Factorizations                       : 0
% 0.19/0.51  # Equation resolutions                 : 0
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 436
% 0.19/0.51  #    Positive orientable unit clauses  : 21
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 9
% 0.19/0.51  #    Non-unit-clauses                  : 406
% 0.19/0.51  # Current number of unprocessed clauses: 3386
% 0.19/0.51  # ...number of literals in the above   : 15842
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 44
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 57124
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 21684
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 677
% 0.19/0.51  # Unit Clause-clause subsumption calls : 219
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 8
% 0.19/0.51  # BW rewrite match successes           : 4
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 110528
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.166 s
% 0.19/0.51  # System time              : 0.005 s
% 0.19/0.51  # Total time               : 0.170 s
% 0.19/0.51  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
