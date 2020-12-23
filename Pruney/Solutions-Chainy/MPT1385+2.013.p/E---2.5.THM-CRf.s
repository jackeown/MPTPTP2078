%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 357 expanded)
%              Number of clauses        :   58 ( 143 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  298 (1579 expanded)
%              Number of equality atoms :   14 (  73 expanded)
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

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ( r2_hidden(X10,X12)
        | ~ r1_tarski(k2_tarski(X10,X11),X12) )
      & ( r2_hidden(X11,X12)
        | ~ r1_tarski(k2_tarski(X10,X11),X12) )
      & ( ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X11,X12)
        | r1_tarski(k2_tarski(X10,X11),X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | k6_domain_1(X21,X22) = k1_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_19,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X26,X27,X28] :
      ( ( ~ m2_connsp_2(X28,X26,X27)
        | r1_tarski(X27,k1_tops_1(X26,X28))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tarski(X27,k1_tops_1(X26,X28))
        | m2_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
      | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) )
    & ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
      | m1_connsp_2(esk3_0,esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_27,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_32,plain,
    ( m2_connsp_2(X1,X2,k1_enumset1(X3,X3,X4))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_enumset1(X3,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X4,k1_tops_1(X2,X1))
    | ~ r2_hidden(X3,k1_tops_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_enumset1(esk2_0,esk2_0,esk2_0) = k6_domain_1(u1_struct_0(esk1_0),esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( ( ~ m1_connsp_2(X25,X23,X24)
        | r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | m1_connsp_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_36,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_connsp_2(X31,X29,X30)
      | m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_37,negated_conjecture,
    ( m2_connsp_2(X1,X2,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(esk2_0,k1_tops_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m2_connsp_2(X1,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_connsp_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_30]),c_0_39]),c_0_40])]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_50,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m2_connsp_2(X34,X32,X33)
      | m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

fof(c_0_51,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_52,negated_conjecture,
    ( ~ m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_55,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_56,plain,(
    ! [X14] : m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_57,plain,(
    ! [X13] : k2_subset_1(X13) = X13 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_58,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(X3,k1_tops_1(X2,X1))
    | ~ m2_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_60,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_63,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_46])).

cnf(c_0_71,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(k1_enumset1(X3,X3,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ m2_connsp_2(X2,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_78,negated_conjecture,
    ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[c_0_49,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,X1)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_33])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_44]),c_0_39]),c_0_40])]),c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_30])]),c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_88]),c_0_46])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_71]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.029 s
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.41  fof(t10_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 0.13/0.41  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.13/0.41  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.41  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.13/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.13/0.41  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.13/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.41  fof(c_0_16, plain, ![X10, X11, X12]:(((r2_hidden(X10,X12)|~r1_tarski(k2_tarski(X10,X11),X12))&(r2_hidden(X11,X12)|~r1_tarski(k2_tarski(X10,X11),X12)))&(~r2_hidden(X10,X12)|~r2_hidden(X11,X12)|r1_tarski(k2_tarski(X10,X11),X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.41  fof(c_0_17, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.41  fof(c_0_18, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|k6_domain_1(X21,X22)=k1_tarski(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.41  fof(c_0_19, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.41  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t10_connsp_2])).
% 0.13/0.41  fof(c_0_21, plain, ![X26, X27, X28]:((~m2_connsp_2(X28,X26,X27)|r1_tarski(X27,k1_tops_1(X26,X28))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_tarski(X27,k1_tops_1(X26,X28))|m2_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.13/0.41  cnf(c_0_22, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  cnf(c_0_24, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~m1_connsp_2(esk3_0,esk1_0,esk2_0))&(m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|m1_connsp_2(esk3_0,esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.13/0.41  cnf(c_0_27, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_28, plain, (r1_tarski(k1_enumset1(X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.41  cnf(c_0_29, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_23])).
% 0.13/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  fof(c_0_31, plain, ![X19, X20]:(v1_xboole_0(X19)|~m1_subset_1(X20,X19)|m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.41  cnf(c_0_32, plain, (m2_connsp_2(X1,X2,k1_enumset1(X3,X3,X4))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k1_enumset1(X3,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X4,k1_tops_1(X2,X1))|~r2_hidden(X3,k1_tops_1(X2,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (k1_enumset1(esk2_0,esk2_0,esk2_0)=k6_domain_1(u1_struct_0(esk1_0),esk2_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.41  cnf(c_0_34, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.41  fof(c_0_35, plain, ![X23, X24, X25]:((~m1_connsp_2(X25,X23,X24)|r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X24,k1_tops_1(X23,X25))|m1_connsp_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.13/0.41  fof(c_0_36, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,u1_struct_0(X29))|(~m1_connsp_2(X31,X29,X30)|m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (m2_connsp_2(X1,X2,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(esk2_0,k1_tops_1(X2,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.13/0.41  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_41, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.41  cnf(c_0_43, negated_conjecture, (m2_connsp_2(X1,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_45, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~m1_connsp_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_30]), c_0_39]), c_0_40])]), c_0_46])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  fof(c_0_50, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~m2_connsp_2(X34,X32,X33)|m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.13/0.41  fof(c_0_51, plain, ![X18]:(v2_struct_0(X18)|~l1_struct_0(X18)|~v1_xboole_0(u1_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (~m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.41  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  fof(c_0_55, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.41  fof(c_0_56, plain, ![X14]:m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.41  fof(c_0_57, plain, ![X13]:k2_subset_1(X13)=X13, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.41  fof(c_0_58, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.41  cnf(c_0_59, plain, (r1_tarski(X3,k1_tops_1(X2,X1))|~m2_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_60, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.41  cnf(c_0_61, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|~m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.41  fof(c_0_63, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.41  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_54, c_0_23])).
% 0.13/0.41  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.41  cnf(c_0_66, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.41  cnf(c_0_67, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.41  cnf(c_0_68, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_69, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (~m1_connsp_2(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_46])).
% 0.13/0.41  cnf(c_0_71, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.41  cnf(c_0_72, plain, (r2_hidden(X1,X2)|~m1_subset_1(k1_enumset1(X3,X3,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.41  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.41  cnf(c_0_74, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (~m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_40])])).
% 0.13/0.41  cnf(c_0_76, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(X1,k1_tops_1(esk1_0,X2))|~m2_connsp_2(X2,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_38]), c_0_39]), c_0_40])])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(sr,[status(thm)],[c_0_49, c_0_75])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_76, c_0_33])).
% 0.13/0.41  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.41  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.13/0.41  cnf(c_0_83, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_84, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,X1)|~r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_33])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.13/0.41  cnf(c_0_86, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_44]), c_0_39]), c_0_40])]), c_0_46])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.13/0.41  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_30])]), c_0_75])).
% 0.13/0.41  cnf(c_0_89, negated_conjecture, (~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_88]), c_0_46])).
% 0.13/0.41  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_71]), c_0_40])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 91
% 0.13/0.41  # Proof object clause steps            : 58
% 0.13/0.41  # Proof object formula steps           : 33
% 0.13/0.41  # Proof object conjectures             : 33
% 0.13/0.41  # Proof object clause conjectures      : 30
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 25
% 0.13/0.41  # Proof object initial formulas used   : 16
% 0.13/0.41  # Proof object generating inferences   : 26
% 0.13/0.41  # Proof object simplifying inferences  : 32
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 16
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 27
% 0.13/0.41  # Removed in clause preprocessing      : 3
% 0.13/0.41  # Initial clauses in saturation        : 24
% 0.13/0.41  # Processed clauses                    : 298
% 0.13/0.41  # ...of these trivial                  : 1
% 0.13/0.41  # ...subsumed                          : 95
% 0.13/0.41  # ...remaining for further processing  : 202
% 0.13/0.41  # Other redundant clauses eliminated   : 0
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 17
% 0.13/0.41  # Backward-rewritten                   : 50
% 0.13/0.41  # Generated clauses                    : 670
% 0.13/0.41  # ...of the previous two non-trivial   : 626
% 0.13/0.41  # Contextual simplify-reflections      : 5
% 0.13/0.41  # Paramodulations                      : 665
% 0.13/0.41  # Factorizations                       : 4
% 0.13/0.41  # Equation resolutions                 : 0
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 134
% 0.13/0.41  #    Positive orientable unit clauses  : 10
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 3
% 0.13/0.41  #    Non-unit-clauses                  : 121
% 0.13/0.41  # Current number of unprocessed clauses: 351
% 0.13/0.41  # ...number of literals in the above   : 1571
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 71
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 3527
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 1465
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 107
% 0.13/0.41  # Unit Clause-clause subsumption calls : 216
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 7
% 0.13/0.41  # BW rewrite match successes           : 3
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 17851
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.063 s
% 0.13/0.41  # System time              : 0.004 s
% 0.13/0.41  # Total time               : 0.067 s
% 0.13/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
