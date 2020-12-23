%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 151 expanded)
%              Number of clauses        :   27 (  49 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  255 (1347 expanded)
%              Number of equality atoms :   42 ( 161 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :  103 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_8,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | r1_tarski(k1_setfam_1(X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | k6_setfam_1(X8,X9) = k1_setfam_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X16,X17] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(X16,X12)
        | ~ r2_hidden(X16,esk1_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(X16,X12)
        | ~ r2_hidden(X16,esk1_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,X16)
        | ~ r2_hidden(X16,esk1_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(X16,X12)
        | ~ v4_pre_topc(X16,X12)
        | ~ r2_hidden(X13,X16)
        | r2_hidden(X16,esk1_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( k6_setfam_1(u1_struct_0(X12),esk1_3(X12,X13,X14)) = X14
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_4(X12,X13,X14,X17),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(esk2_4(X12,X13,X14,X17),X17)
        | ~ v3_pre_topc(esk2_4(X12,X13,X14,X17),X12)
        | ~ v4_pre_topc(esk2_4(X12,X13,X14,X17),X12)
        | ~ r2_hidden(X13,esk2_4(X12,X13,X14,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk2_4(X12,X13,X14,X17),X12)
        | r2_hidden(esk2_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(esk2_4(X12,X13,X14,X17),X12)
        | r2_hidden(esk2_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,esk2_4(X12,X13,X14,X17))
        | r2_hidden(esk2_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r1_tarski(k6_setfam_1(X1,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0))) = k1_connsp_2(esk3_0,esk4_0)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X2)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_32,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0)
    | k1_connsp_2(esk3_0,esk4_0) != k1_connsp_2(esk3_0,X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_13]),c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk5_0,k1_connsp_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 != k1_connsp_2(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t31_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((v3_pre_topc(X3,X1)&v4_pre_topc(X3,X1))&r2_hidden(X2,X3))&r1_tarski(X3,k1_connsp_2(X1,X2)))=>X3=k1_connsp_2(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_connsp_2)).
% 0.20/0.38  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.20/0.38  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.20/0.38  fof(d7_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k1_connsp_2(X1,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))&![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X5,X4)<=>((v3_pre_topc(X5,X1)&v4_pre_topc(X5,X1))&r2_hidden(X2,X5)))))&k6_setfam_1(u1_struct_0(X1),X4)=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_connsp_2)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((v3_pre_topc(X3,X1)&v4_pre_topc(X3,X1))&r2_hidden(X2,X3))&r1_tarski(X3,k1_connsp_2(X1,X2)))=>X3=k1_connsp_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_connsp_2])).
% 0.20/0.38  fof(c_0_7, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))|m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((((v3_pre_topc(esk5_0,esk3_0)&v4_pre_topc(esk5_0,esk3_0))&r2_hidden(esk4_0,esk5_0))&r1_tarski(esk5_0,k1_connsp_2(esk3_0,esk4_0)))&esk5_0!=k1_connsp_2(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X10, X11]:(~r2_hidden(X10,X11)|r1_tarski(k1_setfam_1(X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.38  fof(c_0_10, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))|k6_setfam_1(X8,X9)=k1_setfam_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.20/0.38  fof(c_0_11, plain, ![X12, X13, X14, X16, X17]:((((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((((v3_pre_topc(X16,X12)|~r2_hidden(X16,esk1_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(v4_pre_topc(X16,X12)|~r2_hidden(X16,esk1_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(r2_hidden(X13,X16)|~r2_hidden(X16,esk1_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~v3_pre_topc(X16,X12)|~v4_pre_topc(X16,X12)|~r2_hidden(X13,X16)|r2_hidden(X16,esk1_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(k6_setfam_1(u1_struct_0(X12),esk1_3(X12,X13,X14))=X14|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&((m1_subset_1(esk2_4(X12,X13,X14,X17),k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((~r2_hidden(esk2_4(X12,X13,X14,X17),X17)|(~v3_pre_topc(esk2_4(X12,X13,X14,X17),X12)|~v4_pre_topc(esk2_4(X12,X13,X14,X17),X12)|~r2_hidden(X13,esk2_4(X12,X13,X14,X17)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((v3_pre_topc(esk2_4(X12,X13,X14,X17),X12)|r2_hidden(esk2_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(v4_pre_topc(esk2_4(X12,X13,X14,X17),X12)|r2_hidden(esk2_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(r2_hidden(X13,esk2_4(X12,X13,X14,X17))|r2_hidden(esk2_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).
% 0.20/0.38  cnf(c_0_12, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_17, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_18, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_19, plain, (k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3))=X3|v2_struct_0(X1)|X3!=k1_connsp_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(k1_connsp_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.38  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_struct_0(X1)|X3!=k1_connsp_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(k6_setfam_1(X1,X2),X3)|~r2_hidden(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (k6_setfam_1(u1_struct_0(esk3_0),esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0)))=k1_connsp_2(esk3_0,esk4_0)|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,X1,k1_connsp_2(esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(X1,esk1_3(X2,X3,X4))|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v4_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X4!=k1_connsp_2(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X2)|~r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk1_3(esk3_0,X2,k1_connsp_2(esk3_0,esk4_0)))|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X2)|~v4_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_connsp_2(esk3_0,esk4_0),X1)|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X2)|~v4_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v4_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_32, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0)|k1_connsp_2(esk3_0,esk4_0)!=k1_connsp_2(esk3_0,X1)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_connsp_2(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_13]), c_0_34])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(esk5_0,k1_connsp_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk5_0!=k1_connsp_2(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_38]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 40
% 0.20/0.38  # Proof object clause steps            : 27
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 22
% 0.20/0.38  # Proof object clause conjectures      : 19
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 25
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 67
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 45
% 0.20/0.38  # ...of the previous two non-trivial   : 33
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 43
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 37
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 24
% 0.20/0.38  # Current number of unprocessed clauses: 17
% 0.20/0.38  # ...number of literals in the above   : 115
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 28
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 537
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 18
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4421
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
