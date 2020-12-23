%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 675 expanded)
%              Number of clauses        :   51 ( 245 expanded)
%              Number of leaves         :   16 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 (3241 expanded)
%              Number of equality atoms :   18 ( 357 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t40_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_xboole_0(X2,X3)
                  & v3_pre_topc(X2,X1) )
               => r1_xboole_0(X2,k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t55_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
               => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                  | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_tex_2])).

fof(c_0_17,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | r2_hidden(X28,k1_connsp_2(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v3_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))
    & k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | m1_subset_1(k1_connsp_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_20,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | k6_domain_1(X21,X22) = k1_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_27,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_xboole_0(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,k1_connsp_2(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(k1_connsp_2(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = k6_domain_1(u1_struct_0(esk3_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | m1_subset_1(k2_pre_topc(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = k6_domain_1(u1_struct_0(esk3_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_46,c_0_44])).

fof(c_0_52,plain,(
    ! [X23,X24] :
      ( ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | v4_pre_topc(k2_pre_topc(X23,X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

fof(c_0_53,plain,(
    ! [X11,X12] :
      ( r2_hidden(X11,X12)
      | r1_xboole_0(k1_tarski(X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_54,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ r1_xboole_0(X33,X34)
      | ~ v3_pre_topc(X33,X32)
      | r1_xboole_0(X33,k2_pre_topc(X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k6_domain_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_44])).

fof(c_0_57,plain,(
    ! [X29,X30] :
      ( ( ~ v3_tdlat_3(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v4_pre_topc(X30,X29)
        | v3_pre_topc(X30,X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk2_1(X29),k1_zfmisc_1(u1_struct_0(X29)))
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v4_pre_topc(esk2_1(X29),X29)
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v3_pre_topc(esk2_1(X29),X29)
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_50]),c_0_51])).

cnf(c_0_60,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_61,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24])])).

cnf(c_0_67,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_23]),c_0_24])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23]),c_0_24])])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_23]),c_0_24])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k2_tarski(X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_74,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ v3_tdlat_3(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ m1_subset_1(X37,u1_struct_0(X35))
      | ~ r2_hidden(X36,k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X37)))
      | k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X36)) = k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_66]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_56])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))
    | r2_hidden(esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)) = k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_22]),c_0_67]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_78]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_37]),c_0_81])]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.13/0.39  # and selection function SelectGrCQArEqFirst.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 0.13/0.39  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.13/0.39  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.13/0.39  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.13/0.39  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.13/0.39  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.39  fof(t40_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_xboole_0(X2,X3)&v3_pre_topc(X2,X1))=>r1_xboole_0(X2,k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 0.13/0.39  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.13/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.39  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 0.13/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.13/0.39  fof(c_0_17, plain, ![X27, X28]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|r2_hidden(X28,k1_connsp_2(X27,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.13/0.39  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))&k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X25, X26]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,u1_struct_0(X25))|m1_subset_1(k1_connsp_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.13/0.39  fof(c_0_20, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_21, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  fof(c_0_26, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|k6_domain_1(X21,X22)=k1_tarski(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.39  fof(c_0_27, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_28, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.39  fof(c_0_29, plain, ![X15, X16]:(~v1_xboole_0(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_xboole_0(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,k1_connsp_2(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.39  cnf(c_0_33, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  fof(c_0_35, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.13/0.39  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(k1_connsp_2(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(k1_connsp_2(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_41, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.39  cnf(c_0_42, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_22])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=k6_domain_1(u1_struct_0(esk3_0),esk5_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 0.13/0.39  cnf(c_0_47, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_34])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.39  fof(c_0_49, plain, ![X19, X20]:(~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|m1_subset_1(k2_pre_topc(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[c_0_45, c_0_44])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=k6_domain_1(u1_struct_0(esk3_0),esk5_0)), inference(sr,[status(thm)],[c_0_46, c_0_44])).
% 0.13/0.39  fof(c_0_52, plain, ![X23, X24]:(~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|v4_pre_topc(k2_pre_topc(X23,X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.13/0.39  fof(c_0_53, plain, ![X11, X12]:(r2_hidden(X11,X12)|r1_xboole_0(k1_tarski(X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.39  fof(c_0_54, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~r1_xboole_0(X33,X34)|~v3_pre_topc(X33,X32)|r1_xboole_0(X33,k2_pre_topc(X32,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k6_domain_1(u1_struct_0(esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_44])).
% 0.13/0.39  fof(c_0_57, plain, ![X29, X30]:((~v3_tdlat_3(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~v4_pre_topc(X30,X29)|v3_pre_topc(X30,X29)))|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((m1_subset_1(esk2_1(X29),k1_zfmisc_1(u1_struct_0(X29)))|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((v4_pre_topc(esk2_1(X29),X29)|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(~v3_pre_topc(esk2_1(X29),X29)|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.13/0.39  cnf(c_0_58, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_50]), c_0_51])).
% 0.13/0.39  cnf(c_0_60, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  fof(c_0_61, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.39  cnf(c_0_62, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_63, plain, (r1_xboole_0(X2,k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_xboole_0(X2,X3)|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_65, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_23]), c_0_24])])).
% 0.13/0.39  cnf(c_0_69, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_70, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_62, c_0_34])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (r1_xboole_0(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_23]), c_0_24])])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_23]), c_0_24])])).
% 0.13/0.39  cnf(c_0_73, plain, (r1_xboole_0(X1,k2_tarski(X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.39  fof(c_0_74, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~v3_tdlat_3(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~m1_subset_1(X37,u1_struct_0(X35))|(~r2_hidden(X36,k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X37)))|k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X36))=k2_pre_topc(X35,k6_domain_1(u1_struct_0(X35),X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))|~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_66]), c_0_72])])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_56])).
% 0.13/0.39  cnf(c_0_77, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))|r2_hidden(esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1))=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_22]), c_0_67]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_78]), c_0_79])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_37]), c_0_81])]), c_0_82]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 84
% 0.13/0.39  # Proof object clause steps            : 51
% 0.13/0.39  # Proof object formula steps           : 33
% 0.13/0.39  # Proof object conjectures             : 35
% 0.13/0.39  # Proof object clause conjectures      : 32
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 23
% 0.13/0.39  # Proof object initial formulas used   : 16
% 0.13/0.39  # Proof object generating inferences   : 21
% 0.13/0.39  # Proof object simplifying inferences  : 42
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 16
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 27
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 26
% 0.13/0.39  # Processed clauses                    : 237
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 35
% 0.13/0.39  # ...remaining for further processing  : 202
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 6
% 0.13/0.39  # Generated clauses                    : 449
% 0.13/0.39  # ...of the previous two non-trivial   : 437
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 446
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 167
% 0.13/0.39  #    Positive orientable unit clauses  : 69
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 9
% 0.13/0.39  #    Non-unit-clauses                  : 89
% 0.13/0.39  # Current number of unprocessed clauses: 242
% 0.13/0.39  # ...number of literals in the above   : 594
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 36
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1466
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 983
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.39  # Unit Clause-clause subsumption calls : 143
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 190
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 16707
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.046 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.050 s
% 0.13/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
