%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 241 expanded)
%              Number of clauses        :   49 (  95 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  359 (1319 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

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

fof(cc23_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2)
              & v2_tdlat_3(X2) )
           => ( ~ v2_struct_0(X2)
              & ~ v1_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc23_tex_2)).

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

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | m1_subset_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X14,X15] :
      ( ( ~ r1_tarski(k1_tarski(X14),X15)
        | r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X14,X15)
        | r1_tarski(k1_tarski(X14),X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_24,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ v2_tdlat_3(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | v2_tdlat_3(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_28,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | ~ v2_tdlat_3(X31)
      | v2_pre_topc(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_29,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | v2_tex_2(k6_domain_1(u1_struct_0(X39),X40),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X34)
      | v1_xboole_0(X35)
      | ~ v1_zfmisc_1(X35)
      | ~ r1_tarski(X34,X35)
      | X34 = X35 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X13] : ~ v1_xboole_0(k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_39,plain,(
    ! [X29,X30] :
      ( ( ~ v2_struct_0(X30)
        | v2_struct_0(X30)
        | v7_struct_0(X30)
        | ~ v2_tdlat_3(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v1_tdlat_3(X30)
        | v2_struct_0(X30)
        | v7_struct_0(X30)
        | ~ v2_tdlat_3(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc23_tex_2])])])])])).

fof(c_0_40,plain,(
    ! [X36,X37] :
      ( ( ~ v2_struct_0(esk2_2(X36,X37))
        | ~ v2_tex_2(X37,X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v1_pre_topc(esk2_2(X36,X37))
        | ~ v2_tex_2(X37,X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v1_tdlat_3(esk2_2(X36,X37))
        | ~ v2_tex_2(X37,X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_pre_topc(esk2_2(X36,X37),X36)
        | ~ v2_tex_2(X37,X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( X37 = u1_struct_0(esk2_2(X36,X37))
        | ~ v2_tex_2(X37,X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tarski(esk1_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_51,plain,(
    ! [X23] :
      ( ~ v7_struct_0(X23)
      | ~ l1_struct_0(X23)
      | v1_zfmisc_1(u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( v1_tdlat_3(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( v2_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_57,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_58,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( v2_tex_2(k1_tarski(X1),X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31])).

cnf(c_0_60,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_tarski(esk1_1(esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_50])).

cnf(c_0_63,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(esk2_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_66,plain,
    ( v2_tdlat_3(esk2_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_42])).

cnf(c_0_67,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_69,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk1_1(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk2_2(X1,X2))
    | ~ l1_struct_0(esk2_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_42])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0)
    | ~ v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])]),c_0_73]),c_0_50]),c_0_74])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_42])).

cnf(c_0_81,negated_conjecture,
    ( v2_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_zfmisc_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_79]),c_0_81]),c_0_72]),c_0_26])]),c_0_73]),c_0_82]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.029 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.20/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.46  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.46  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.46  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.46  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.46  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.20/0.46  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.20/0.46  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.20/0.46  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.20/0.46  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.46  fof(cc23_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(((~(v2_struct_0(X2))&~(v7_struct_0(X2)))&v2_tdlat_3(X2))=>(~(v2_struct_0(X2))&~(v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc23_tex_2)).
% 0.20/0.46  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.20/0.46  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.46  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.20/0.46  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.46  fof(c_0_17, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.20/0.46  fof(c_0_18, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.46  fof(c_0_19, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v2_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&((~v2_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0))&(v2_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.20/0.46  fof(c_0_20, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|k6_domain_1(X24,X25)=k1_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.46  fof(c_0_21, plain, ![X16, X17]:(~r2_hidden(X16,X17)|m1_subset_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.46  fof(c_0_22, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.46  fof(c_0_23, plain, ![X14, X15]:((~r1_tarski(k1_tarski(X14),X15)|r2_hidden(X14,X15))&(~r2_hidden(X14,X15)|r1_tarski(k1_tarski(X14),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.46  fof(c_0_24, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.46  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  fof(c_0_27, plain, ![X32, X33]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~v2_tdlat_3(X32)|~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|v2_tdlat_3(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.20/0.46  fof(c_0_28, plain, ![X31]:(~l1_pre_topc(X31)|(~v2_tdlat_3(X31)|v2_pre_topc(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.20/0.46  fof(c_0_29, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,u1_struct_0(X39))|v2_tex_2(k6_domain_1(u1_struct_0(X39),X40),X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.20/0.46  cnf(c_0_30, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_33, plain, ![X34, X35]:(v1_xboole_0(X34)|(v1_xboole_0(X35)|~v1_zfmisc_1(X35)|(~r1_tarski(X34,X35)|X34=X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.20/0.46  cnf(c_0_34, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_35, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_36, plain, ![X13]:~v1_xboole_0(k1_tarski(X13)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.46  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.46  fof(c_0_39, plain, ![X29, X30]:((~v2_struct_0(X30)|(v2_struct_0(X30)|v7_struct_0(X30)|~v2_tdlat_3(X30))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~l1_pre_topc(X29)))&(~v1_tdlat_3(X30)|(v2_struct_0(X30)|v7_struct_0(X30)|~v2_tdlat_3(X30))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc23_tex_2])])])])])).
% 0.20/0.46  fof(c_0_40, plain, ![X36, X37]:(((((~v2_struct_0(esk2_2(X36,X37))|~v2_tex_2(X37,X36)|(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(v1_pre_topc(esk2_2(X36,X37))|~v2_tex_2(X37,X36)|(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(v1_tdlat_3(esk2_2(X36,X37))|~v2_tex_2(X37,X36)|(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(m1_pre_topc(esk2_2(X36,X37),X36)|~v2_tex_2(X37,X36)|(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(X37=u1_struct_0(esk2_2(X36,X37))|~v2_tex_2(X37,X36)|(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.20/0.46  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  cnf(c_0_42, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  fof(c_0_43, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.46  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_45, plain, (k6_domain_1(X1,X2)=k1_tarski(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.46  cnf(c_0_46, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_47, plain, (r1_tarski(k1_tarski(esk1_1(X1)),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.46  cnf(c_0_48, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.46  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.46  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  fof(c_0_51, plain, ![X23]:(~v7_struct_0(X23)|~l1_struct_0(X23)|v1_zfmisc_1(u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.20/0.46  cnf(c_0_52, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v2_struct_0(X2)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  cnf(c_0_53, plain, (m1_pre_topc(esk2_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_54, plain, (v1_tdlat_3(esk2_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_55, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_56, plain, (v2_tdlat_3(X1)|v2_struct_0(X2)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.46  fof(c_0_57, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.46  cnf(c_0_58, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.46  cnf(c_0_59, plain, (v2_tex_2(k1_tarski(X1),X2)|v2_struct_0(X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31])).
% 0.20/0.46  cnf(c_0_60, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.20/0.46  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_tarski(esk1_1(esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_50])).
% 0.20/0.46  cnf(c_0_63, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.46  cnf(c_0_64, plain, (X1=u1_struct_0(esk2_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_65, plain, (v2_struct_0(X1)|v7_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(esk2_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])).
% 0.20/0.46  cnf(c_0_66, plain, (v2_tdlat_3(esk2_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_42])).
% 0.20/0.46  cnf(c_0_67, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.46  cnf(c_0_68, plain, (v2_struct_0(X1)|l1_pre_topc(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_58, c_0_53])).
% 0.20/0.46  cnf(c_0_69, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|v1_xboole_0(X1)|~v2_pre_topc(X2)|~v1_zfmisc_1(X1)|~l1_pre_topc(X2)|~r2_hidden(esk1_1(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_1(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_72, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_75, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk2_2(X1,X2))|~l1_struct_0(esk2_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.46  cnf(c_0_76, plain, (v2_struct_0(X1)|v7_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_42])).
% 0.20/0.46  cnf(c_0_77, plain, (v2_struct_0(X1)|l1_struct_0(esk2_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_79, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])]), c_0_73]), c_0_50]), c_0_74])).
% 0.20/0.46  cnf(c_0_80, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_42])).
% 0.20/0.46  cnf(c_0_81, negated_conjecture, (v2_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_82, negated_conjecture, (~v1_zfmisc_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_79]), c_0_81]), c_0_72]), c_0_26])]), c_0_73]), c_0_82]), c_0_50]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 84
% 0.20/0.46  # Proof object clause steps            : 49
% 0.20/0.46  # Proof object formula steps           : 35
% 0.20/0.46  # Proof object conjectures             : 18
% 0.20/0.46  # Proof object clause conjectures      : 15
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 29
% 0.20/0.46  # Proof object initial formulas used   : 17
% 0.20/0.46  # Proof object generating inferences   : 18
% 0.20/0.46  # Proof object simplifying inferences  : 26
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 19
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 37
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 36
% 0.20/0.46  # Processed clauses                    : 1530
% 0.20/0.46  # ...of these trivial                  : 1
% 0.20/0.46  # ...subsumed                          : 1178
% 0.20/0.46  # ...remaining for further processing  : 351
% 0.20/0.46  # Other redundant clauses eliminated   : 2
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 21
% 0.20/0.46  # Backward-rewritten                   : 18
% 0.20/0.46  # Generated clauses                    : 2791
% 0.20/0.46  # ...of the previous two non-trivial   : 2408
% 0.20/0.46  # Contextual simplify-reflections      : 25
% 0.20/0.46  # Paramodulations                      : 2789
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 2
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 275
% 0.20/0.46  #    Positive orientable unit clauses  : 15
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 7
% 0.20/0.46  #    Non-unit-clauses                  : 253
% 0.20/0.46  # Current number of unprocessed clauses: 880
% 0.20/0.46  # ...number of literals in the above   : 4586
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 74
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 32686
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 9923
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 692
% 0.20/0.46  # Unit Clause-clause subsumption calls : 559
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 13
% 0.20/0.46  # BW rewrite match successes           : 1
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 51188
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.111 s
% 0.20/0.46  # System time              : 0.006 s
% 0.20/0.46  # Total time               : 0.117 s
% 0.20/0.46  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
