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
% DateTime   : Thu Dec  3 11:21:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 613 expanded)
%              Number of clauses        :   60 ( 221 expanded)
%              Number of leaves         :   18 ( 158 expanded)
%              Depth                    :   13
%              Number of atoms          :  323 (4625 expanded)
%              Number of equality atoms :   50 ( 649 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t77_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t76_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_18,plain,(
    ! [X54,X55,X56] :
      ( ( ~ v4_tex_2(X55,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
        | X56 != u1_struct_0(X55)
        | v3_tex_2(X56,X54)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) )
      & ( m1_subset_1(esk2_2(X54,X55),k1_zfmisc_1(u1_struct_0(X54)))
        | v4_tex_2(X55,X54)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) )
      & ( esk2_2(X54,X55) = u1_struct_0(X55)
        | v4_tex_2(X55,X54)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) )
      & ( ~ v3_tex_2(esk2_2(X54,X55),X54)
        | v4_tex_2(X55,X54)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

fof(c_0_19,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_pre_topc(X53,X52)
      | m1_subset_1(u1_struct_0(X53),k1_zfmisc_1(u1_struct_0(X52))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_tex_2(X2,X1)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v5_pre_topc(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v3_borsuk_1(X3,X1,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( X4 = X5
                           => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tex_2])).

cnf(c_0_21,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v3_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_tex_2(esk4_0,esk3_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & v5_pre_topc(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v3_borsuk_1(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk7_0
    & k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_24,plain,(
    ! [X58,X59] :
      ( v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | ~ v1_xboole_0(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | ~ v3_tex_2(X59,X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_25,plain,
    ( v3_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_31,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ r2_hidden(X42,X41)
      | r2_hidden(X42,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X50,X51] :
      ( v1_xboole_0(X50)
      | ~ m1_subset_1(X51,X50)
      | k6_domain_1(X50,X51) = k1_tarski(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_38,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_41,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_42,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_43,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_44,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_28])]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_48,plain,(
    ! [X60,X61,X62,X63,X64] :
      ( v2_struct_0(X60)
      | ~ v2_pre_topc(X60)
      | ~ v3_tdlat_3(X60)
      | ~ l1_pre_topc(X60)
      | v2_struct_0(X61)
      | ~ v4_tex_2(X61,X60)
      | ~ m1_pre_topc(X61,X60)
      | ~ v1_funct_1(X62)
      | ~ v1_funct_2(X62,u1_struct_0(X60),u1_struct_0(X61))
      | ~ v5_pre_topc(X62,X60,X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X60),u1_struct_0(X61))))
      | ~ v3_borsuk_1(X62,X60,X61)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X60)))
      | X63 != X64
      | k8_relset_1(u1_struct_0(X60),u1_struct_0(X61),X62,X63) = k2_pre_topc(X60,X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).

fof(c_0_49,plain,(
    ! [X47,X48,X49] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_pre_topc(X48,X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_50,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | m1_subset_1(k1_tarski(X43),k1_zfmisc_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_59,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | X4 != X5 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( v3_borsuk_1(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_80,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk4_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_85,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1) = k2_pre_topc(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_34]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk3_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_27]),c_0_28])])).

cnf(c_0_89,negated_conjecture,
    ( k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk6_0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk6_0) = k6_domain_1(u1_struct_0(esk3_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_61]),c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_90]),c_0_46]),c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_92]),c_0_46])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_22]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v4_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_tex_2(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 0.19/0.37  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.37  fof(t77_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 0.19/0.37  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.38  fof(t76_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 0.19/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.38  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(c_0_18, plain, ![X54, X55, X56]:((~v4_tex_2(X55,X54)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))|(X56!=u1_struct_0(X55)|v3_tex_2(X56,X54)))|~m1_pre_topc(X55,X54)|(v2_struct_0(X54)|~l1_pre_topc(X54)))&((m1_subset_1(esk2_2(X54,X55),k1_zfmisc_1(u1_struct_0(X54)))|v4_tex_2(X55,X54)|~m1_pre_topc(X55,X54)|(v2_struct_0(X54)|~l1_pre_topc(X54)))&((esk2_2(X54,X55)=u1_struct_0(X55)|v4_tex_2(X55,X54)|~m1_pre_topc(X55,X54)|(v2_struct_0(X54)|~l1_pre_topc(X54)))&(~v3_tex_2(esk2_2(X54,X55),X54)|v4_tex_2(X55,X54)|~m1_pre_topc(X55,X54)|(v2_struct_0(X54)|~l1_pre_topc(X54)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).
% 0.19/0.38  fof(c_0_19, plain, ![X52, X53]:(~l1_pre_topc(X52)|(~m1_pre_topc(X53,X52)|m1_subset_1(u1_struct_0(X53),k1_zfmisc_1(u1_struct_0(X52))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)))))))))), inference(assume_negation,[status(cth)],[t77_tex_2])).
% 0.19/0.38  cnf(c_0_21, plain, (v3_tex_2(X3,X2)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_22, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v4_tex_2(esk4_0,esk3_0))&m1_pre_topc(esk4_0,esk3_0))&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&v5_pre_topc(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(v3_borsuk_1(esk5_0,esk3_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&(esk6_0=esk7_0&k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk7_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.19/0.38  fof(c_0_24, plain, ![X58, X59]:(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)|(~v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|~v3_tex_2(X59,X58))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.19/0.38  cnf(c_0_25, plain, (v3_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v4_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_30, plain, ![X45, X46]:(~m1_subset_1(X45,X46)|(v1_xboole_0(X46)|r2_hidden(X45,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  fof(c_0_31, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|(~r2_hidden(X42,X41)|r2_hidden(X42,X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v3_tex_2(u1_struct_0(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_35, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_37, plain, ![X50, X51]:(v1_xboole_0(X50)|~m1_subset_1(X51,X50)|k6_domain_1(X50,X51)=k1_tarski(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.38  fof(c_0_38, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_39, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_40, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_41, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_42, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.38  fof(c_0_43, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.38  fof(c_0_44, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_28])]), c_0_29])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  fof(c_0_48, plain, ![X60, X61, X62, X63, X64]:(v2_struct_0(X60)|~v2_pre_topc(X60)|~v3_tdlat_3(X60)|~l1_pre_topc(X60)|(v2_struct_0(X61)|~v4_tex_2(X61,X60)|~m1_pre_topc(X61,X60)|(~v1_funct_1(X62)|~v1_funct_2(X62,u1_struct_0(X60),u1_struct_0(X61))|~v5_pre_topc(X62,X60,X61)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X60),u1_struct_0(X61))))|(~v3_borsuk_1(X62,X60,X61)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X60)))|(X63!=X64|k8_relset_1(u1_struct_0(X60),u1_struct_0(X61),X62,X63)=k2_pre_topc(X60,X64)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).
% 0.19/0.38  fof(c_0_49, plain, ![X47, X48, X49]:(~l1_pre_topc(X47)|(~m1_pre_topc(X48,X47)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.38  fof(c_0_50, plain, ![X43, X44]:(~r2_hidden(X43,X44)|m1_subset_1(k1_tarski(X43),k1_zfmisc_1(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_53, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_54, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_55, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_56, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_57, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.38  fof(c_0_59, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.38  cnf(c_0_60, plain, (r2_hidden(X1,u1_struct_0(X2))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_borsuk_1(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|X4!=X5), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_65, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.38  cnf(c_0_66, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_67, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])).
% 0.19/0.38  cnf(c_0_68, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_72, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~v3_borsuk_1(X3,X1,X2)|~v5_pre_topc(X3,X1,X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]), c_0_65])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (v3_borsuk_1(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_80, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_52]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk4_0),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_36])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_70])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk6_0))), inference(rw,[status(thm)],[c_0_71, c_0_63])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)=k2_pre_topc(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77]), c_0_78]), c_0_34]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_79])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk3_0),esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_70])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1))|v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_27]), c_0_28])])).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, (k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk6_0))|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.38  cnf(c_0_90, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk6_0)=k6_domain_1(u1_struct_0(esk3_0),esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_81, c_0_86])).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_61]), c_0_46])).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_88])).
% 0.19/0.38  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.38  cnf(c_0_94, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_90]), c_0_46]), c_0_92])).
% 0.19/0.38  cnf(c_0_95, negated_conjecture, (~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_92]), c_0_46])).
% 0.19/0.38  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_22]), c_0_27]), c_0_28])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 97
% 0.19/0.38  # Proof object clause steps            : 60
% 0.19/0.38  # Proof object formula steps           : 37
% 0.19/0.38  # Proof object conjectures             : 41
% 0.19/0.38  # Proof object clause conjectures      : 38
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 33
% 0.19/0.38  # Proof object initial formulas used   : 18
% 0.19/0.38  # Proof object generating inferences   : 21
% 0.19/0.38  # Proof object simplifying inferences  : 51
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 18
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 37
% 0.19/0.38  # Removed in clause preprocessing      : 7
% 0.19/0.38  # Initial clauses in saturation        : 30
% 0.19/0.38  # Processed clauses                    : 128
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 10
% 0.19/0.38  # ...remaining for further processing  : 118
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 7
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 125
% 0.19/0.38  # ...of the previous two non-trivial   : 117
% 0.19/0.38  # Contextual simplify-reflections      : 8
% 0.19/0.38  # Paramodulations                      : 123
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
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
% 0.19/0.38  # Current number of processed clauses  : 79
% 0.19/0.38  #    Positive orientable unit clauses  : 14
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 61
% 0.19/0.38  # Current number of unprocessed clauses: 44
% 0.19/0.38  # ...number of literals in the above   : 172
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 44
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 807
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 195
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 25
% 0.19/0.38  # Unit Clause-clause subsumption calls : 17
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5786
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
