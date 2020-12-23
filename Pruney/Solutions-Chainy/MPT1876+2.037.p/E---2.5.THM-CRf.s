%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 326 expanded)
%              Number of clauses        :   56 ( 136 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  395 (1510 expanded)
%              Number of equality atoms :   17 (  42 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc6_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_tdlat_3(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc2_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & v2_tdlat_3(X1) )
       => ( ~ v2_struct_0(X1)
          & v7_struct_0(X1)
          & v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

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

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_20,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
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

fof(c_0_24,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X34)
      | v1_xboole_0(X35)
      | ~ v1_zfmisc_1(X35)
      | ~ r1_tarski(X34,X35)
      | X34 = X35 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_25,plain,(
    ! [X14] : ~ v1_xboole_0(k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_26,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ v2_tdlat_3(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | v2_tdlat_3(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_31,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | ~ v2_tdlat_3(X27)
      | v2_pre_topc(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_32,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_33,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tarski(X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X28] :
      ( ( ~ v2_struct_0(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) )
      & ( v7_struct_0(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) )
      & ( v2_pre_topc(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X31,X32] :
      ( ( ~ v2_struct_0(esk3_2(X31,X32))
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_pre_topc(esk3_2(X31,X32))
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_pre_topc(esk3_2(X31,X32),X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31) )
      & ( X32 = u1_struct_0(esk3_2(X31,X32))
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_44,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_45,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v2_tex_2(X38,X36)
        | v1_tdlat_3(X37)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ v1_tdlat_3(X37)
        | v2_tex_2(X38,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_46,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | v2_tex_2(k6_domain_1(u1_struct_0(X39),X40),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35]),c_0_36])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(k1_tarski(X1)),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_39])).

fof(c_0_52,plain,(
    ! [X24] :
      ( ~ v7_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v1_zfmisc_1(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_53,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_58,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_36])).

cnf(c_0_61,plain,
    ( k1_tarski(esk1_1(k1_tarski(X1))) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_63,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_69,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( v2_tex_2(k1_tarski(X1),X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_48])).

cnf(c_0_72,plain,
    ( k1_tarski(esk1_1(k1_tarski(esk1_1(X1)))) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(k1_tarski(X1)),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v7_struct_0(esk3_2(X1,X2))
    | ~ l1_struct_0(esk3_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v1_tdlat_3(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_67])).

cnf(c_0_78,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X3)
    | ~ m1_pre_topc(esk3_2(X1,X2),X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_64]),c_0_68])).

cnf(c_0_79,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk1_1(k1_tarski(esk1_1(X1))),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk1_1(k1_tarski(esk1_1(esk5_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_38]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_84,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v1_tdlat_3(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_86,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_55])).

cnf(c_0_87,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82])]),c_0_83]),c_0_74]),c_0_84])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( v2_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_zfmisc_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_90]),c_0_82]),c_0_39])]),c_0_83]),c_0_91]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.21/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.029 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.47  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.21/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.47  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.21/0.47  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.21/0.47  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.21/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.47  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.21/0.47  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.21/0.47  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.21/0.47  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.47  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 0.21/0.47  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.21/0.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.47  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.21/0.47  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.21/0.47  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.21/0.47  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.47  fof(c_0_18, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.47  fof(c_0_19, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.21/0.47  fof(c_0_20, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.47  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.47  cnf(c_0_22, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  fof(c_0_23, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.21/0.47  fof(c_0_24, plain, ![X34, X35]:(v1_xboole_0(X34)|(v1_xboole_0(X35)|~v1_zfmisc_1(X35)|(~r1_tarski(X34,X35)|X34=X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.21/0.47  fof(c_0_25, plain, ![X14]:~v1_xboole_0(k1_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.21/0.47  fof(c_0_26, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.47  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_28, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.47  fof(c_0_29, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v2_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0))&(v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.21/0.47  fof(c_0_30, plain, ![X29, X30]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~v2_tdlat_3(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|v2_tdlat_3(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.21/0.47  fof(c_0_31, plain, ![X27]:(~l1_pre_topc(X27)|(~v2_tdlat_3(X27)|v2_pre_topc(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.21/0.47  fof(c_0_32, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.21/0.47  fof(c_0_33, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.47  cnf(c_0_34, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.47  cnf(c_0_35, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_tarski(X3))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.47  cnf(c_0_38, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  fof(c_0_40, plain, ![X28]:(((~v2_struct_0(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28))&(v7_struct_0(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28)))&(v2_pre_topc(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 0.21/0.47  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.47  cnf(c_0_42, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.47  fof(c_0_43, plain, ![X31, X32]:((((~v2_struct_0(esk3_2(X31,X32))|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~l1_pre_topc(X31)))&(v1_pre_topc(esk3_2(X31,X32))|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~l1_pre_topc(X31))))&(m1_pre_topc(esk3_2(X31,X32),X31)|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~l1_pre_topc(X31))))&(X32=u1_struct_0(esk3_2(X31,X32))|(v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(v2_struct_0(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.21/0.47  fof(c_0_44, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.47  fof(c_0_45, plain, ![X36, X37, X38]:((~v2_tex_2(X38,X36)|v1_tdlat_3(X37)|X38!=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~l1_pre_topc(X36)))&(~v1_tdlat_3(X37)|v2_tex_2(X38,X36)|X38!=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.21/0.47  fof(c_0_46, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,u1_struct_0(X39))|v2_tex_2(k6_domain_1(u1_struct_0(X39),X40),X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.21/0.47  cnf(c_0_47, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.47  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.47  cnf(c_0_49, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35]), c_0_36])).
% 0.21/0.47  cnf(c_0_50, plain, (r2_hidden(esk1_1(k1_tarski(X1)),X2)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])).
% 0.21/0.47  cnf(c_0_51, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_39])).
% 0.21/0.47  fof(c_0_52, plain, ![X24]:(~v7_struct_0(X24)|~l1_struct_0(X24)|v1_zfmisc_1(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.21/0.47  cnf(c_0_53, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.47  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.47  cnf(c_0_55, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.47  cnf(c_0_56, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.47  fof(c_0_57, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.47  cnf(c_0_58, plain, (v1_tdlat_3(X3)|v2_struct_0(X3)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|X1!=u1_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.47  cnf(c_0_59, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.47  cnf(c_0_60, plain, (k6_domain_1(X1,X2)=k1_tarski(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_36])).
% 0.21/0.47  cnf(c_0_61, plain, (k1_tarski(esk1_1(k1_tarski(X1)))=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_51])).
% 0.21/0.47  cnf(c_0_63, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.47  cnf(c_0_64, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.47  cnf(c_0_65, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_53, c_0_42])).
% 0.21/0.47  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.47  cnf(c_0_67, plain, (v2_struct_0(X1)|l1_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.21/0.47  cnf(c_0_68, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.47  cnf(c_0_69, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.47  cnf(c_0_70, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_tex_2(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.47  cnf(c_0_71, plain, (v2_tex_2(k1_tarski(X1),X2)|v2_struct_0(X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_48])).
% 0.21/0.47  cnf(c_0_72, plain, (k1_tarski(esk1_1(k1_tarski(esk1_1(X1))))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.21/0.47  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(k1_tarski(X1)),u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_50])).
% 0.21/0.47  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_75, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v7_struct_0(esk3_2(X1,X2))|~l1_struct_0(esk3_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.47  cnf(c_0_76, plain, (v2_struct_0(X1)|v7_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v1_tdlat_3(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])).
% 0.21/0.47  cnf(c_0_77, plain, (v2_struct_0(X1)|l1_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_69, c_0_67])).
% 0.21/0.47  cnf(c_0_78, plain, (v1_tdlat_3(esk3_2(X1,X2))|v2_struct_0(X1)|v2_struct_0(X3)|v1_xboole_0(X2)|~v2_tex_2(X2,X3)|~m1_pre_topc(esk3_2(X1,X2),X3)|~l1_pre_topc(X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_64]), c_0_68])).
% 0.21/0.47  cnf(c_0_79, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|v1_xboole_0(X1)|~v2_pre_topc(X2)|~v1_zfmisc_1(X1)|~l1_pre_topc(X2)|~r2_hidden(esk1_1(k1_tarski(esk1_1(X1))),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.47  cnf(c_0_80, negated_conjecture, (r2_hidden(esk1_1(k1_tarski(esk1_1(esk5_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_38]), c_0_74])).
% 0.21/0.47  cnf(c_0_81, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_82, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_83, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_84, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_85, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v1_tdlat_3(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.21/0.47  cnf(c_0_86, plain, (v1_tdlat_3(esk3_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_78, c_0_55])).
% 0.21/0.47  cnf(c_0_87, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_88, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82])]), c_0_83]), c_0_74]), c_0_84])).
% 0.21/0.47  cnf(c_0_89, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.47  cnf(c_0_90, negated_conjecture, (v2_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_91, negated_conjecture, (~v1_zfmisc_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.21/0.47  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_90]), c_0_82]), c_0_39])]), c_0_83]), c_0_91]), c_0_74]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 93
% 0.21/0.47  # Proof object clause steps            : 56
% 0.21/0.47  # Proof object formula steps           : 37
% 0.21/0.47  # Proof object conjectures             : 18
% 0.21/0.47  # Proof object clause conjectures      : 15
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 28
% 0.21/0.47  # Proof object initial formulas used   : 18
% 0.21/0.47  # Proof object generating inferences   : 24
% 0.21/0.47  # Proof object simplifying inferences  : 28
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 18
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 35
% 0.21/0.47  # Removed in clause preprocessing      : 2
% 0.21/0.47  # Initial clauses in saturation        : 33
% 0.21/0.47  # Processed clauses                    : 1247
% 0.21/0.47  # ...of these trivial                  : 0
% 0.21/0.47  # ...subsumed                          : 846
% 0.21/0.47  # ...remaining for further processing  : 401
% 0.21/0.47  # Other redundant clauses eliminated   : 2
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 48
% 0.21/0.47  # Backward-rewritten                   : 10
% 0.21/0.47  # Generated clauses                    : 2925
% 0.21/0.47  # ...of the previous two non-trivial   : 2639
% 0.21/0.47  # Contextual simplify-reflections      : 40
% 0.21/0.47  # Paramodulations                      : 2921
% 0.21/0.47  # Factorizations                       : 2
% 0.21/0.47  # Equation resolutions                 : 2
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 308
% 0.21/0.47  #    Positive orientable unit clauses  : 14
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 8
% 0.21/0.47  #    Non-unit-clauses                  : 286
% 0.21/0.47  # Current number of unprocessed clauses: 1216
% 0.21/0.47  # ...number of literals in the above   : 5634
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 91
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 16619
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 6334
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 619
% 0.21/0.47  # Unit Clause-clause subsumption calls : 440
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 20
% 0.21/0.47  # BW rewrite match successes           : 3
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 54554
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.120 s
% 0.21/0.47  # System time              : 0.002 s
% 0.21/0.47  # Total time               : 0.122 s
% 0.21/0.47  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
