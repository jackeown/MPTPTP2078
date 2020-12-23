%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1859+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:55 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  107 (1035 expanded)
%              Number of clauses        :   74 ( 433 expanded)
%              Number of leaves         :   16 ( 256 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 (3904 expanded)
%              Number of equality atoms :   45 ( 752 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( X2 = u1_struct_0(X1)
             => ( v2_tex_2(X2,X1)
              <=> v1_tdlat_3(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_tex_2])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ v1_tdlat_3(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v3_pre_topc(X34,X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk4_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | v1_tdlat_3(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ v3_pre_topc(esk4_1(X33),X33)
        | v1_tdlat_3(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_18,plain,(
    ! [X29] : k9_setfam_1(X29) = k1_zfmisc_1(X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_19,plain,(
    ! [X19,X20,X21,X24] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r1_tarski(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk2_3(X19,X20,X21),X19)
        | ~ r1_tarski(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( k9_subset_1(u1_struct_0(X19),X20,esk2_3(X19,X20,X21)) = X21
        | ~ r1_tarski(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(esk3_2(X19,X20),X20)
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v3_pre_topc(X24,X19)
        | k9_subset_1(u1_struct_0(X19),X20,X24) != esk3_2(X19,X20)
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & esk6_0 = u1_struct_0(esk5_0)
    & ( ~ v2_tex_2(esk6_0,esk5_0)
      | ~ v1_tdlat_3(esk5_0) )
    & ( v2_tex_2(esk6_0,esk5_0)
      | v1_tdlat_3(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_tdlat_3(X5)
      | v2_pre_topc(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | k9_subset_1(X30,X31,X32) = k3_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_27,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk3_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v2_tex_2(X2,X1)
    | m1_subset_1(esk3_2(X1,X2),k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 = u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k9_setfam_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_35,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | m1_subset_1(k9_subset_1(X25,X26,X27),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_36,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v2_tex_2(X3,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk3_2(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2)))
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,X1),k9_setfam_1(esk6_0))
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k9_setfam_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k9_setfam_1(X2)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k9_setfam_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | k9_subset_1(esk6_0,X1,X2) != esk3_2(esk5_0,X1)
    | ~ v3_pre_topc(X2,esk5_0)
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0))
    | ~ m1_subset_1(X2,k9_setfam_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33])])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0))
    | ~ v1_tdlat_3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_33])])).

cnf(c_0_49,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk6_0),k9_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | v1_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_51,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_52,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k3_xboole_0(X38,X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_53,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk2_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k9_setfam_1(X2)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_56,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k9_setfam_1(X2))
    | ~ m1_subset_1(X1,k9_setfam_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_22]),c_0_22])).

cnf(c_0_57,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | k9_subset_1(esk6_0,esk6_0,X1) != esk3_2(esk5_0,esk6_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | v3_pre_topc(esk3_2(esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk2_3(X1,X2,X3)) = X3
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_22]),c_0_22])).

cnf(c_0_63,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,k9_setfam_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | k9_subset_1(esk6_0,esk6_0,esk3_2(esk5_0,esk6_0)) != esk3_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | r1_tarski(esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

fof(c_0_67,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | m1_subset_1(u1_pre_topc(X28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_68,plain,(
    ! [X17,X18] :
      ( ( ~ v3_pre_topc(X18,X17)
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(X18,u1_pre_topc(X17))
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,esk2_3(X2,X1,X3)) = X3
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_63])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k9_setfam_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | k3_xboole_0(esk6_0,esk3_2(esk5_0,esk6_0)) != esk3_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_57]),c_0_66])).

cnf(c_0_73,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_74,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_76,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | m1_subset_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_77,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,plain,
    ( esk2_3(X1,X2,X3) = X3
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk2_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,X1,X2),esk6_0)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0))
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_33])]),c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_69]),c_0_66])).

cnf(c_0_81,plain,
    ( m1_subset_1(u1_pre_topc(X1),k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_22]),c_0_22])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_22])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_22]),c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,X1) = X1
    | ~ r1_tarski(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_32]),c_0_41]),c_0_33]),c_0_41])])).

fof(c_0_88,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k9_setfam_1(k9_setfam_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_32]),c_0_33])])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(esk1_2(X1,u1_pre_topc(X2)),X2)
    | ~ m1_subset_1(esk1_2(X1,u1_pre_topc(X2)),k9_setfam_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k9_setfam_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_80]),c_0_32]),c_0_32]),c_0_41]),c_0_33])]),c_0_54])).

fof(c_0_93,plain,(
    ! [X10] :
      ( ( ~ v1_tdlat_3(X10)
        | u1_pre_topc(X10) = k9_setfam_1(u1_struct_0(X10))
        | ~ l1_pre_topc(X10) )
      & ( u1_pre_topc(X10) != k9_setfam_1(u1_struct_0(X10))
        | v1_tdlat_3(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k9_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_89])).

cnf(c_0_96,plain,
    ( r1_tarski(k9_setfam_1(u1_struct_0(X1)),u1_pre_topc(X1))
    | ~ v3_pre_topc(esk1_2(k9_setfam_1(u1_struct_0(X1)),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_46])).

cnf(c_0_98,plain,
    ( r1_tarski(esk1_2(k9_setfam_1(X1),X2),X1)
    | r1_tarski(k9_setfam_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_91])).

cnf(c_0_99,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( k9_setfam_1(esk6_0) = u1_pre_topc(esk5_0)
    | ~ r1_tarski(k9_setfam_1(esk6_0),u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k9_setfam_1(esk6_0),u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_32]),c_0_33]),c_0_32])]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0)
    | ~ v1_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( v1_tdlat_3(esk5_0)
    | k9_setfam_1(esk6_0) != u1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_32]),c_0_33])])).

cnf(c_0_104,negated_conjecture,
    ( k9_setfam_1(esk6_0) = u1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_tdlat_3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_80])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])]),c_0_105]),
    [proof]).

%------------------------------------------------------------------------------
