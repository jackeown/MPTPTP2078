%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:46 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 456 expanded)
%              Number of clauses        :   46 ( 180 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  235 (1867 expanded)
%              Number of equality atoms :   26 ( 236 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v3_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))
    & k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_22,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | k2_pre_topc(X21,k2_pre_topc(X21,X22)) = k2_pre_topc(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k6_domain_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_32])).

fof(c_0_41,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_37]),c_0_32])).

fof(c_0_43,plain,(
    ! [X23,X24] :
      ( ( ~ v4_pre_topc(X24,X23)
        | k2_pre_topc(X23,X24) = X24
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_pre_topc(X23)
        | k2_pre_topc(X23,X24) != X24
        | v4_pre_topc(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_44,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X11,X12] :
      ( r2_hidden(X11,X12)
      | r1_xboole_0(k1_tarski(X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ r1_xboole_0(X31,X32)
      | ~ v3_pre_topc(X31,X30)
      | r1_xboole_0(X31,k2_pre_topc(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = k6_domain_1(u1_struct_0(esk3_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])).

fof(c_0_51,plain,(
    ! [X27,X28] :
      ( ( ~ v3_tdlat_3(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v4_pre_topc(X28,X27)
        | v3_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk2_1(X27),k1_zfmisc_1(u1_struct_0(X27)))
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( v4_pre_topc(esk2_1(X27),X27)
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(esk2_1(X27),X27)
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_52,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k2_pre_topc(esk3_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) = k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_20])])).

fof(c_0_56,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_20]),c_0_55])])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_29])).

fof(c_0_65,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ v3_tdlat_3(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | ~ r2_hidden(X34,k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X35)))
      | k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X34)) = k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_54]),c_0_20])])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_61]),c_0_54]),c_0_20])]),c_0_62])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,k2_tarski(X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_55]),c_0_67])]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk5_0))
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_50])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)) = k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_61]),c_0_54]),c_0_20])]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_37]),c_0_74])]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.14/0.37  # and selection function SelectGrCQArEqFirst.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.017 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 0.14/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.37  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.37  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.14/0.37  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.14/0.37  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.14/0.37  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.14/0.37  fof(t40_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_xboole_0(X2,X3)&v3_pre_topc(X2,X1))=>r1_xboole_0(X2,k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 0.14/0.37  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.14/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.37  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 0.14/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.14/0.37  fof(c_0_16, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.37  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))&k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.14/0.37  fof(c_0_18, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.37  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_21, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.14/0.37  fof(c_0_22, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_23, plain, ![X15, X16]:(~m1_subset_1(X15,X16)|(v1_xboole_0(X16)|r2_hidden(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_27, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.37  cnf(c_0_28, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_30, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.14/0.37  cnf(c_0_33, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  cnf(c_0_34, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.14/0.37  cnf(c_0_36, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_38, plain, ![X21, X22]:(~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|k2_pre_topc(X21,k2_pre_topc(X21,X22))=k2_pre_topc(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k6_domain_1(u1_struct_0(esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_32])).
% 0.14/0.37  fof(c_0_41, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_37]), c_0_32])).
% 0.14/0.37  fof(c_0_43, plain, ![X23, X24]:((~v4_pre_topc(X24,X23)|k2_pre_topc(X23,X24)=X24|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v2_pre_topc(X23)|k2_pre_topc(X23,X24)!=X24|v4_pre_topc(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.14/0.37  cnf(c_0_44, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.37  cnf(c_0_46, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.37  fof(c_0_47, plain, ![X11, X12]:(r2_hidden(X11,X12)|r1_xboole_0(k1_tarski(X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.14/0.37  fof(c_0_48, plain, ![X30, X31, X32]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(~r1_xboole_0(X31,X32)|~v3_pre_topc(X31,X30)|r1_xboole_0(X31,k2_pre_topc(X30,X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_42])).
% 0.14/0.37  cnf(c_0_50, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=k6_domain_1(u1_struct_0(esk3_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32])).
% 0.14/0.37  fof(c_0_51, plain, ![X27, X28]:((~v3_tdlat_3(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v4_pre_topc(X28,X27)|v3_pre_topc(X28,X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((m1_subset_1(esk2_1(X27),k1_zfmisc_1(u1_struct_0(X27)))|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((v4_pre_topc(esk2_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~v3_pre_topc(esk2_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.14/0.37  cnf(c_0_52, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (k2_pre_topc(esk3_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_20])])).
% 0.14/0.37  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_20])])).
% 0.14/0.37  fof(c_0_56, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.37  cnf(c_0_57, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.37  cnf(c_0_58, plain, (r1_xboole_0(X2,k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_xboole_0(X2,X3)|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.37  cnf(c_0_59, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.14/0.37  cnf(c_0_60, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_62, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_20]), c_0_55])])).
% 0.14/0.37  cnf(c_0_63, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.37  cnf(c_0_64, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_57, c_0_29])).
% 0.14/0.37  fof(c_0_65, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~v3_tdlat_3(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,u1_struct_0(X33))|(~m1_subset_1(X35,u1_struct_0(X33))|(~r2_hidden(X34,k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X35)))|k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X34))=k2_pre_topc(X33,k6_domain_1(u1_struct_0(X33),X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.14/0.37  cnf(c_0_66, negated_conjecture, (r1_xboole_0(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_54]), c_0_20])])).
% 0.14/0.37  cnf(c_0_67, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_55]), c_0_61]), c_0_54]), c_0_20])]), c_0_62])])).
% 0.14/0.37  cnf(c_0_68, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_69, plain, (r1_xboole_0(X1,k2_tarski(X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.14/0.37  cnf(c_0_70, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.14/0.37  cnf(c_0_71, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k6_domain_1(u1_struct_0(esk3_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_55]), c_0_67])]), c_0_68])).
% 0.14/0.37  cnf(c_0_72, negated_conjecture, (r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk3_0),esk5_0))|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_50])).
% 0.14/0.37  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1))=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_31]), c_0_61]), c_0_54]), c_0_20])]), c_0_26])).
% 0.14/0.37  cnf(c_0_74, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.14/0.37  cnf(c_0_75, negated_conjecture, (k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))!=k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_37]), c_0_74])]), c_0_75]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 77
% 0.14/0.37  # Proof object clause steps            : 46
% 0.14/0.37  # Proof object formula steps           : 31
% 0.14/0.37  # Proof object conjectures             : 31
% 0.14/0.37  # Proof object clause conjectures      : 28
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 22
% 0.14/0.37  # Proof object initial formulas used   : 15
% 0.14/0.37  # Proof object generating inferences   : 19
% 0.14/0.37  # Proof object simplifying inferences  : 38
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 16
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 28
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 27
% 0.14/0.37  # Processed clauses                    : 120
% 0.14/0.37  # ...of these trivial                  : 5
% 0.14/0.37  # ...subsumed                          : 11
% 0.14/0.37  # ...remaining for further processing  : 104
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 7
% 0.14/0.37  # Generated clauses                    : 101
% 0.14/0.37  # ...of the previous two non-trivial   : 99
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 101
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 70
% 0.14/0.37  #    Positive orientable unit clauses  : 22
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 7
% 0.14/0.37  #    Non-unit-clauses                  : 41
% 0.14/0.37  # Current number of unprocessed clauses: 31
% 0.14/0.37  # ...number of literals in the above   : 86
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 35
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 598
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 270
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.14/0.37  # Unit Clause-clause subsumption calls : 7
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 7
% 0.14/0.37  # BW rewrite match successes           : 3
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 5057
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.018 s
% 0.14/0.37  # System time              : 0.006 s
% 0.14/0.37  # Total time               : 0.024 s
% 0.14/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
