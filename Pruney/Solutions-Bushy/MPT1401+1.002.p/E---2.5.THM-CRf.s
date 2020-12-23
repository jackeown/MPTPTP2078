%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1401+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:14 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 159 expanded)
%              Number of clauses        :   31 (  53 expanded)
%              Number of leaves         :    7 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 (1367 expanded)
%              Number of equality atoms :   43 ( 162 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :  103 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X3,X1)
                  & v4_pre_topc(X3,X1)
                  & r2_hidden(X2,X3)
                  & r1_tarski(X3,k1_connsp_2(X1,X2)) )
               => X3 = k1_connsp_2(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d7_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k1_connsp_2(X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                    & ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X5,X4)
                        <=> ( v3_pre_topc(X5,X1)
                            & v4_pre_topc(X5,X1)
                            & r2_hidden(X2,X5) ) ) )
                    & k6_setfam_1(u1_struct_0(X1),X4) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_pre_topc(X3,X1)
                    & v4_pre_topc(X3,X1)
                    & r2_hidden(X2,X3)
                    & r1_tarski(X3,k1_connsp_2(X1,X2)) )
                 => X3 = k1_connsp_2(X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_connsp_2])).

fof(c_0_8,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | m1_subset_1(k1_connsp_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v3_pre_topc(esk5_0,esk3_0)
    & v4_pre_topc(esk5_0,esk3_0)
    & r2_hidden(esk4_0,esk5_0)
    & r1_tarski(esk5_0,k1_connsp_2(esk3_0,esk4_0))
    & esk5_0 != k1_connsp_2(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | r1_tarski(k1_setfam_1(X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))
      | k6_setfam_1(X17,X18) = k1_setfam_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_12,plain,(
    ! [X8,X9,X10,X12,X13] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(X12,X8)
        | ~ r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v4_pre_topc(X12,X8)
        | ~ r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X9,X12)
        | ~ r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ v3_pre_topc(X12,X8)
        | ~ v4_pre_topc(X12,X8)
        | ~ r2_hidden(X9,X12)
        | r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( k6_setfam_1(u1_struct_0(X8),esk1_3(X8,X9,X10)) = X10
        | X10 != k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_4(X8,X9,X10,X13),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k6_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ v3_pre_topc(esk2_4(X8,X9,X10,X13),X8)
        | ~ v4_pre_topc(esk2_4(X8,X9,X10,X13),X8)
        | ~ r2_hidden(X9,esk2_4(X8,X9,X10,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k6_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(esk2_4(X8,X9,X10,X13),X8)
        | r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k6_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v4_pre_topc(esk2_4(X8,X9,X10,X13),X8)
        | r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k6_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X9,esk2_4(X8,X9,X10,X13))
        | r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k6_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_2(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r1_tarski(k6_setfam_1(X1,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0))) = k1_connsp_2(esk3_0,esk4_0)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X4))
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_0,k1_connsp_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 != k1_connsp_2(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k1_connsp_2(esk3_0,esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).

%------------------------------------------------------------------------------
