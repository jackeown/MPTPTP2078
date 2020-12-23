%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : connsp_2__t31_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 154 expanded)
%              Number of clauses        :   29 (  51 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 (1345 expanded)
%              Number of equality atoms :   47 ( 163 expanded)
%              Maximal formula depth    :   26 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',t31_connsp_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',d10_xboole_0)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',t4_setfam_1)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',dt_k1_connsp_2)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',redefinition_k6_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',d7_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t31_connsp_2.p',t4_subset)).

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
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_9,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | r1_tarski(k1_setfam_1(X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | m1_subset_1(k1_connsp_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_pre_topc(esk3_0,esk1_0)
    & v4_pre_topc(esk3_0,esk1_0)
    & r2_hidden(esk2_0,esk3_0)
    & r1_tarski(esk3_0,k1_connsp_2(esk1_0,esk2_0))
    & esk3_0 != k1_connsp_2(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | k6_setfam_1(X29,X30) = k1_setfam_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X17,X18] :
      ( ( m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(X17,X13)
        | ~ r2_hidden(X17,esk4_3(X13,X14,X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v4_pre_topc(X17,X13)
        | ~ r2_hidden(X17,esk4_3(X13,X14,X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(X14,X17)
        | ~ r2_hidden(X17,esk4_3(X13,X14,X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(X17,X13)
        | ~ v4_pre_topc(X17,X13)
        | ~ r2_hidden(X14,X17)
        | r2_hidden(X17,esk4_3(X13,X14,X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( k6_setfam_1(u1_struct_0(X13),esk4_3(X13,X14,X15)) = X15
        | X15 != k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk5_4(X13,X14,X15,X18),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | k6_setfam_1(u1_struct_0(X13),X18) != X15
        | X15 = k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(esk5_4(X13,X14,X15,X18),X18)
        | ~ v3_pre_topc(esk5_4(X13,X14,X15,X18),X13)
        | ~ v4_pre_topc(esk5_4(X13,X14,X15,X18),X13)
        | ~ r2_hidden(X14,esk5_4(X13,X14,X15,X18))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | k6_setfam_1(u1_struct_0(X13),X18) != X15
        | X15 = k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk5_4(X13,X14,X15,X18),X13)
        | r2_hidden(esk5_4(X13,X14,X15,X18),X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | k6_setfam_1(u1_struct_0(X13),X18) != X15
        | X15 = k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v4_pre_topc(esk5_4(X13,X14,X15,X18),X13)
        | r2_hidden(esk5_4(X13,X14,X15,X18),X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | k6_setfam_1(u1_struct_0(X13),X18) != X15
        | X15 = k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(X14,esk5_4(X13,X14,X15,X18))
        | r2_hidden(esk5_4(X13,X14,X15,X18),X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | k6_setfam_1(u1_struct_0(X13),X18) != X15
        | X15 = k1_connsp_2(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_22,plain,
    ( X1 = k1_setfam_1(X2)
    | ~ r1_tarski(X1,k1_setfam_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_23,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk4_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X4))
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( X1 = k6_setfam_1(X2,X3)
    | ~ r1_tarski(X1,k6_setfam_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk4_3(esk1_0,X1,k1_connsp_2(esk1_0,esk2_0))) = k1_connsp_2(esk1_0,esk2_0)
    | k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,X1,k1_connsp_2(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X4))
    | v2_struct_0(X2)
    | X4 != k1_connsp_2(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_connsp_2(esk1_0,esk2_0)
    | k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X2)
    | ~ r1_tarski(X1,k1_connsp_2(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_3(esk1_0,X2,k1_connsp_2(esk1_0,esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk4_3(esk1_0,X2,k1_connsp_2(esk1_0,esk2_0)))
    | k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k1_connsp_2(esk1_0,esk2_0)
    | k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X2)
    | ~ r1_tarski(X1,k1_connsp_2(esk1_0,esk2_0))
    | ~ r2_hidden(X2,X1)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,k1_connsp_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 != k1_connsp_2(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( k1_connsp_2(esk1_0,esk2_0) != k1_connsp_2(esk1_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
