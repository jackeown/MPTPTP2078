%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:32 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 982 expanded)
%              Number of clauses        :   60 ( 402 expanded)
%              Number of leaves         :   17 ( 243 expanded)
%              Depth                    :   14
%              Number of atoms          :  296 (3981 expanded)
%              Number of equality atoms :   16 ( 209 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t10_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
              <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,X13)
        | ~ r1_tarski(k2_tarski(X11,X12),X13) )
      & ( r2_hidden(X12,X13)
        | ~ r1_tarski(k2_tarski(X11,X12),X13) )
      & ( ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X12,X13)
        | r1_tarski(k2_tarski(X11,X12),X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_20,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
                <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_connsp_2])).

fof(c_0_22,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_23,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29] :
      ( ( ~ m1_connsp_2(X29,X27,X28)
        | r2_hidden(X28,k1_tops_1(X27,X29))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r2_hidden(X28,k1_tops_1(X27,X29))
        | m1_connsp_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_connsp_2(X35,X33,X34)
      | m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
      | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) )
    & ( m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
      | m1_connsp_2(esk4_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | m1_subset_1(k6_domain_1(X23,X24),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_48,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_49,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_50,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(k1_enumset1(X3,X3,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k6_domain_1(u1_struct_0(esk2_0),esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_54,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m2_connsp_2(X32,X30,X31)
        | r1_tarski(X31,k1_tops_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tarski(X31,k1_tops_1(X30,X32))
        | m2_connsp_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_62,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_connsp_2(X1,esk2_0,esk3_0)
    | ~ v1_xboole_0(k1_tops_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( m2_connsp_2(X1,X2,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_tops_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0),k1_zfmisc_1(k1_tops_1(esk2_0,X1)))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_63]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_40]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46])]),c_0_47])).

fof(c_0_71,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m2_connsp_2(X38,X36,X37)
      | m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

cnf(c_0_72,negated_conjecture,
    ( m2_connsp_2(X1,esk2_0,k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0)
    | ~ m1_subset_1(k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_45]),c_0_46])]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0) = k1_enumset1(esk3_0,esk3_0,esk3_0)
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_63]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,plain,
    ( r1_tarski(X3,k1_tops_1(X2,X1))
    | ~ m2_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_77,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( m2_connsp_2(X1,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0)
    | ~ m1_subset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k6_domain_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[c_0_61,c_0_74])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_27])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( ~ m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( m2_connsp_2(X1,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_79]),c_0_80])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,k1_enumset1(X1,X1,X4))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_enumset1(X1,X1,X4),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(X1,X2))
    | ~ m2_connsp_2(X2,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_45]),c_0_46]),c_0_80])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_40])]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.31  % Computer   : n005.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:57:02 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.17/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.17/0.41  #
% 0.17/0.41  # Preprocessing time       : 0.029 s
% 0.17/0.41  
% 0.17/0.41  # Proof found!
% 0.17/0.41  # SZS status Theorem
% 0.17/0.41  # SZS output start CNFRefutation
% 0.17/0.41  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.17/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.17/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.41  fof(t10_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 0.17/0.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.17/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.17/0.41  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.17/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.17/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.17/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.17/0.41  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.17/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.17/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.17/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.17/0.41  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.17/0.41  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.17/0.41  fof(c_0_17, plain, ![X11, X12, X13]:(((r2_hidden(X11,X13)|~r1_tarski(k2_tarski(X11,X12),X13))&(r2_hidden(X12,X13)|~r1_tarski(k2_tarski(X11,X12),X13)))&(~r2_hidden(X11,X13)|~r2_hidden(X12,X13)|r1_tarski(k2_tarski(X11,X12),X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.17/0.41  fof(c_0_18, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.41  fof(c_0_19, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.17/0.41  fof(c_0_20, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.41  fof(c_0_21, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t10_connsp_2])).
% 0.17/0.41  fof(c_0_22, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.17/0.41  fof(c_0_23, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.17/0.41  fof(c_0_24, plain, ![X27, X28, X29]:((~m1_connsp_2(X29,X27,X28)|r2_hidden(X28,k1_tops_1(X27,X29))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r2_hidden(X28,k1_tops_1(X27,X29))|m1_connsp_2(X29,X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.17/0.41  fof(c_0_25, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33))|(~m1_connsp_2(X35,X33,X34)|m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.17/0.41  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.41  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.41  fof(c_0_28, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.17/0.41  cnf(c_0_29, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.41  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.41  fof(c_0_31, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~m1_connsp_2(esk4_0,esk2_0,esk3_0))&(m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|m1_connsp_2(esk4_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.17/0.41  fof(c_0_32, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.17/0.41  cnf(c_0_33, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.41  cnf(c_0_34, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.41  cnf(c_0_35, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.41  cnf(c_0_36, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.41  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.41  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.41  cnf(c_0_39, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_27])).
% 0.17/0.41  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  fof(c_0_41, plain, ![X23, X24]:(v1_xboole_0(X23)|~m1_subset_1(X24,X23)|m1_subset_1(k6_domain_1(X23,X24),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.17/0.41  cnf(c_0_42, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.41  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.17/0.41  cnf(c_0_44, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_35, c_0_36])).
% 0.17/0.41  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  fof(c_0_48, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.17/0.41  fof(c_0_49, plain, ![X22]:(v2_struct_0(X22)|~l1_struct_0(X22)|~v1_xboole_0(u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.17/0.41  fof(c_0_50, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.17/0.41  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~m1_subset_1(k1_enumset1(X3,X3,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.41  cnf(c_0_52, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k6_domain_1(u1_struct_0(esk2_0),esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.17/0.41  cnf(c_0_53, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.17/0.41  fof(c_0_54, plain, ![X30, X31, X32]:((~m2_connsp_2(X32,X30,X31)|r1_tarski(X31,k1_tops_1(X30,X32))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~r1_tarski(X31,k1_tops_1(X30,X32))|m2_connsp_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.17/0.41  cnf(c_0_55, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.17/0.41  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_45]), c_0_46])]), c_0_47])).
% 0.17/0.41  cnf(c_0_57, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.41  cnf(c_0_58, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.41  cnf(c_0_59, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.17/0.41  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_0,X1)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.17/0.41  cnf(c_0_61, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 0.17/0.41  cnf(c_0_62, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.41  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_tops_1(esk2_0,X1))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.17/0.41  cnf(c_0_64, negated_conjecture, (~m1_connsp_2(X1,esk2_0,esk3_0)|~v1_xboole_0(k1_tops_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.17/0.41  cnf(c_0_65, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.41  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.17/0.41  cnf(c_0_67, plain, (m2_connsp_2(X1,X2,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_tops_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 0.17/0.41  cnf(c_0_68, negated_conjecture, (m1_subset_1(k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0),k1_zfmisc_1(k1_tops_1(esk2_0,X1)))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_63]), c_0_64])).
% 0.17/0.41  cnf(c_0_69, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_40]), c_0_45]), c_0_46])]), c_0_47])).
% 0.17/0.41  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_46])]), c_0_47])).
% 0.17/0.41  fof(c_0_71, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m2_connsp_2(X38,X36,X37)|m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.17/0.41  cnf(c_0_72, negated_conjecture, (m2_connsp_2(X1,esk2_0,k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0))|~m1_connsp_2(X1,esk2_0,esk3_0)|~m1_subset_1(k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_45]), c_0_46])]), c_0_69])).
% 0.17/0.41  cnf(c_0_73, negated_conjecture, (k6_domain_1(k1_tops_1(esk2_0,X1),esk3_0)=k1_enumset1(esk3_0,esk3_0,esk3_0)|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_63]), c_0_64])).
% 0.17/0.41  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_57, c_0_70])).
% 0.17/0.41  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.41  cnf(c_0_76, plain, (r1_tarski(X3,k1_tops_1(X2,X1))|~m2_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.41  cnf(c_0_77, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.17/0.41  cnf(c_0_78, negated_conjecture, (m2_connsp_2(X1,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))|~m1_connsp_2(X1,esk2_0,esk3_0)|~m1_subset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.17/0.41  cnf(c_0_79, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k6_domain_1(u1_struct_0(esk2_0),esk3_0)), inference(sr,[status(thm)],[c_0_52, c_0_74])).
% 0.17/0.41  cnf(c_0_80, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[c_0_61, c_0_74])).
% 0.17/0.41  cnf(c_0_81, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_75, c_0_27])).
% 0.17/0.41  cnf(c_0_82, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_76, c_0_77])).
% 0.17/0.41  cnf(c_0_83, negated_conjecture, (~m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  cnf(c_0_84, negated_conjecture, (m2_connsp_2(X1,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_79]), c_0_80])])).
% 0.17/0.41  cnf(c_0_85, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,k1_enumset1(X1,X1,X4))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k1_enumset1(X1,X1,X4),k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.17/0.41  cnf(c_0_86, negated_conjecture, (m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  cnf(c_0_87, negated_conjecture, (~m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.17/0.41  cnf(c_0_88, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.41  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.41  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(X1,X2))|~m2_connsp_2(X2,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_85, c_0_79])).
% 0.17/0.41  cnf(c_0_91, negated_conjecture, (m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[c_0_86, c_0_87])).
% 0.17/0.41  cnf(c_0_92, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_45]), c_0_46])]), c_0_47])).
% 0.17/0.41  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_45]), c_0_46]), c_0_80])])).
% 0.17/0.41  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_40])]), c_0_87]), ['proof']).
% 0.17/0.41  # SZS output end CNFRefutation
% 0.17/0.41  # Proof object total steps             : 95
% 0.17/0.41  # Proof object clause steps            : 60
% 0.17/0.41  # Proof object formula steps           : 35
% 0.17/0.41  # Proof object conjectures             : 33
% 0.17/0.41  # Proof object clause conjectures      : 30
% 0.17/0.41  # Proof object formula conjectures     : 3
% 0.17/0.41  # Proof object initial clauses used    : 26
% 0.17/0.41  # Proof object initial formulas used   : 17
% 0.17/0.41  # Proof object generating inferences   : 24
% 0.17/0.41  # Proof object simplifying inferences  : 42
% 0.17/0.41  # Training examples: 0 positive, 0 negative
% 0.17/0.41  # Parsed axioms                        : 17
% 0.17/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.41  # Initial clauses                      : 29
% 0.17/0.41  # Removed in clause preprocessing      : 3
% 0.17/0.41  # Initial clauses in saturation        : 26
% 0.17/0.41  # Processed clauses                    : 438
% 0.17/0.41  # ...of these trivial                  : 7
% 0.17/0.41  # ...subsumed                          : 146
% 0.17/0.41  # ...remaining for further processing  : 285
% 0.17/0.41  # Other redundant clauses eliminated   : 0
% 0.17/0.41  # Clauses deleted for lack of memory   : 0
% 0.17/0.41  # Backward-subsumed                    : 22
% 0.17/0.41  # Backward-rewritten                   : 10
% 0.17/0.41  # Generated clauses                    : 1445
% 0.17/0.41  # ...of the previous two non-trivial   : 1353
% 0.17/0.41  # Contextual simplify-reflections      : 14
% 0.17/0.41  # Paramodulations                      : 1427
% 0.17/0.41  # Factorizations                       : 0
% 0.17/0.41  # Equation resolutions                 : 0
% 0.17/0.41  # Propositional unsat checks           : 0
% 0.17/0.41  #    Propositional check models        : 0
% 0.17/0.41  #    Propositional check unsatisfiable : 0
% 0.17/0.41  #    Propositional clauses             : 0
% 0.17/0.41  #    Propositional clauses after purity: 0
% 0.17/0.41  #    Propositional unsat core size     : 0
% 0.17/0.41  #    Propositional preprocessing time  : 0.000
% 0.17/0.41  #    Propositional encoding time       : 0.000
% 0.17/0.41  #    Propositional solver time         : 0.000
% 0.17/0.41  #    Success case prop preproc time    : 0.000
% 0.17/0.41  #    Success case prop encoding time   : 0.000
% 0.17/0.41  #    Success case prop solver time     : 0.000
% 0.17/0.41  # Current number of processed clauses  : 235
% 0.17/0.41  #    Positive orientable unit clauses  : 23
% 0.17/0.41  #    Positive unorientable unit clauses: 1
% 0.17/0.41  #    Negative unit clauses             : 10
% 0.17/0.41  #    Non-unit-clauses                  : 201
% 0.17/0.41  # Current number of unprocessed clauses: 854
% 0.17/0.41  # ...number of literals in the above   : 3360
% 0.17/0.41  # Current number of archived formulas  : 0
% 0.17/0.41  # Current number of archived clauses   : 53
% 0.17/0.41  # Clause-clause subsumption calls (NU) : 5324
% 0.17/0.41  # Rec. Clause-clause subsumption calls : 2401
% 0.17/0.41  # Non-unit clause-clause subsumptions  : 161
% 0.17/0.41  # Unit Clause-clause subsumption calls : 437
% 0.17/0.41  # Rewrite failures with RHS unbound    : 31
% 0.17/0.41  # BW rewrite match attempts            : 41
% 0.17/0.41  # BW rewrite match successes           : 18
% 0.17/0.41  # Condensation attempts                : 0
% 0.17/0.41  # Condensation successes               : 0
% 0.17/0.41  # Termbank termtop insertions          : 34702
% 0.17/0.41  
% 0.17/0.41  # -------------------------------------------------
% 0.17/0.41  # User time                : 0.088 s
% 0.17/0.41  # System time              : 0.005 s
% 0.17/0.41  # Total time               : 0.093 s
% 0.17/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
