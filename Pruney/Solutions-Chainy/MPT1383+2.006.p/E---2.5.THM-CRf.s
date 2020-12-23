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
% DateTime   : Thu Dec  3 11:14:27 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   92 (2550 expanded)
%              Number of clauses        :   75 (1026 expanded)
%              Number of leaves         :    8 ( 607 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (16321 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t8_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

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

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(c_0_8,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m1_connsp_2(X3,X1,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & r1_tarski(X4,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_connsp_2])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | r1_tarski(k1_tops_1(X18,X19),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X29] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v3_pre_topc(X29,esk2_0)
        | ~ r1_tarski(X29,esk4_0)
        | ~ r2_hidden(esk3_0,X29) )
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | m1_connsp_2(esk4_0,esk2_0,esk3_0) )
      & ( v3_pre_topc(esk5_0,esk2_0)
        | m1_connsp_2(esk4_0,esk2_0,esk3_0) )
      & ( r1_tarski(esk5_0,esk4_0)
        | m1_connsp_2(esk4_0,esk2_0,esk3_0) )
      & ( r2_hidden(esk3_0,esk5_0)
        | m1_connsp_2(esk4_0,esk2_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | v3_pre_topc(k1_tops_1(X16,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ m1_connsp_2(X2,esk2_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_17]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | r1_tarski(esk5_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_41]),c_0_29])])).

fof(c_0_44,plain,(
    ! [X20,X21,X22] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ v3_pre_topc(X21,X20)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(X21,k1_tops_1(X20,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | r1_tarski(esk5_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),X2)
    | ~ r1_tarski(X2,k1_tops_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_12]),c_0_37])])).

cnf(c_0_54,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_17])]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_22]),c_0_41]),c_0_29])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(k1_tops_1(esk2_0,X2),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X2))
    | ~ r1_tarski(k1_tops_1(esk2_0,X2),esk4_0)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_54]),c_0_29]),c_0_34])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_43])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_56])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | r1_tarski(esk5_0,k1_tops_1(esk2_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_41]),c_0_29])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,X2))
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | r1_tarski(esk5_0,k1_tops_1(esk2_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_0,X1)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_12]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_12]),c_0_37])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,X2)))
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_22]),c_0_57])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))
    | r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_56]),c_0_29])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_72]),c_0_29]),c_0_34])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_29]),c_0_57])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_71]),c_0_56]),c_0_29])])).

cnf(c_0_80,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | r2_hidden(esk3_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk2_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_tops_1(esk2_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( m1_connsp_2(X1,esk2_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X2,k1_tops_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_80]),c_0_17]),c_0_25])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_12])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_84]),c_0_29]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_41]),c_0_29])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_12]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.52/2.69  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YA
% 2.52/2.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.52/2.69  #
% 2.52/2.69  # Preprocessing time       : 0.028 s
% 2.52/2.69  # Presaturation interreduction done
% 2.52/2.69  
% 2.52/2.69  # Proof found!
% 2.52/2.69  # SZS status Theorem
% 2.52/2.69  # SZS output start CNFRefutation
% 2.52/2.69  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.52/2.69  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.52/2.69  fof(t8_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 2.52/2.69  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.52/2.69  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.52/2.69  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.52/2.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.52/2.69  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.52/2.69  fof(c_0_8, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.52/2.69  fof(c_0_9, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.52/2.69  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))))), inference(assume_negation,[status(cth)],[t8_connsp_2])).
% 2.52/2.69  cnf(c_0_11, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 2.52/2.69  cnf(c_0_12, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.52/2.69  fof(c_0_13, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|r1_tarski(k1_tops_1(X18,X19),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 2.52/2.69  fof(c_0_14, negated_conjecture, ![X29]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~m1_connsp_2(esk4_0,esk2_0,esk3_0)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X29,esk2_0)|~r1_tarski(X29,esk4_0)|~r2_hidden(esk3_0,X29)))&((((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|m1_connsp_2(esk4_0,esk2_0,esk3_0))&(v3_pre_topc(esk5_0,esk2_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0)))&(r1_tarski(esk5_0,esk4_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0)))&(r2_hidden(esk3_0,esk5_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 2.52/2.69  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 2.52/2.69  cnf(c_0_16, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.52/2.69  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.69  fof(c_0_18, plain, ![X23, X24, X25]:((~m1_connsp_2(X25,X23,X24)|r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X24,k1_tops_1(X23,X25))|m1_connsp_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 2.52/2.69  fof(c_0_19, plain, ![X16, X17]:(~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v3_pre_topc(k1_tops_1(X16,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 2.52/2.69  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.52/2.69  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 2.52/2.69  cnf(c_0_22, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.52/2.69  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.69  cnf(c_0_24, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.69  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.69  cnf(c_0_26, negated_conjecture, (~m1_connsp_2(esk4_0,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk4_0)|~r2_hidden(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.69  cnf(c_0_27, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.52/2.69  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 2.52/2.70  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_30, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 2.52/2.70  fof(c_0_31, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.52/2.70  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~m1_connsp_2(X2,esk2_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17]), c_0_25])])).
% 2.52/2.70  cnf(c_0_33, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_35, negated_conjecture, (~m1_connsp_2(esk4_0,esk2_0,esk3_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_17]), c_0_25])])).
% 2.52/2.70  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.52/2.70  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 2.52/2.70  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.52/2.70  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29]), c_0_34])])).
% 2.52/2.70  cnf(c_0_40, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 2.52/2.70  cnf(c_0_41, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.52/2.70  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,X1)|r1_tarski(esk5_0,esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.52/2.70  cnf(c_0_43, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_41]), c_0_29])])).
% 2.52/2.70  fof(c_0_44, plain, ![X20, X21, X22]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~v3_pre_topc(X21,X20)|~r1_tarski(X21,X22)|r1_tarski(X21,k1_tops_1(X20,X22)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 2.52/2.70  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_0,X1)|r1_tarski(esk5_0,esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 2.52/2.70  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_43])).
% 2.52/2.70  cnf(c_0_47, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.52/2.70  cnf(c_0_48, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),X2)|~r1_tarski(X2,k1_tops_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_45])).
% 2.52/2.70  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.52/2.70  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.52/2.70  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_12]), c_0_37])])).
% 2.52/2.70  cnf(c_0_54, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_17])]), c_0_49])).
% 2.52/2.70  cnf(c_0_55, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),X1)|~r1_tarski(X1,k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_22]), c_0_41]), c_0_29])])).
% 2.52/2.70  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.52/2.70  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_53])).
% 2.52/2.70  cnf(c_0_58, negated_conjecture, (r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(k1_tops_1(esk2_0,X2),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X2))|~r1_tarski(k1_tops_1(esk2_0,X2),esk4_0)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_54])).
% 2.52/2.70  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_54]), c_0_29]), c_0_34])])).
% 2.52/2.70  cnf(c_0_60, negated_conjecture, (r1_tarski(esk5_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_43])).
% 2.52/2.70  cnf(c_0_61, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 2.52/2.70  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_56])])).
% 2.52/2.70  cnf(c_0_63, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_53])).
% 2.52/2.70  cnf(c_0_64, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 2.52/2.70  cnf(c_0_65, negated_conjecture, (r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|r1_tarski(esk5_0,k1_tops_1(esk2_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)|~r1_tarski(esk5_0,X2)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_41]), c_0_29])])).
% 2.52/2.70  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_60])).
% 2.52/2.70  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,X2))|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_25]), c_0_17])])).
% 2.52/2.70  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_62])).
% 2.52/2.70  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 2.52/2.70  cnf(c_0_70, negated_conjecture, (r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|r1_tarski(esk5_0,k1_tops_1(esk2_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_0,X1)|~r1_tarski(esk5_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_12]), c_0_37])])).
% 2.52/2.70  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_12]), c_0_37])])).
% 2.52/2.70  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.52/2.70  cnf(c_0_73, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,X2)))|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_67])).
% 2.52/2.70  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_22]), c_0_57])])).
% 2.52/2.70  cnf(c_0_75, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_69])).
% 2.52/2.70  cnf(c_0_76, negated_conjecture, (r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))|r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_56]), c_0_29])])).
% 2.52/2.70  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_72]), c_0_29]), c_0_34])])).
% 2.52/2.70  cnf(c_0_78, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_29]), c_0_57])])).
% 2.52/2.70  cnf(c_0_79, negated_conjecture, (r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_71]), c_0_56]), c_0_29])])).
% 2.52/2.70  cnf(c_0_80, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.70  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|r2_hidden(esk3_0,X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_77])).
% 2.52/2.70  cnf(c_0_82, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk2_0,esk5_0)))), inference(spm,[status(thm)],[c_0_28, c_0_78])).
% 2.52/2.70  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_tops_1(esk2_0,esk5_0)))), inference(spm,[status(thm)],[c_0_20, c_0_79])).
% 2.52/2.70  cnf(c_0_84, negated_conjecture, (m1_connsp_2(X1,esk2_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X2,k1_tops_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_80]), c_0_17]), c_0_25])])).
% 2.52/2.70  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|r2_hidden(esk3_0,X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_12])).
% 2.52/2.70  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 2.52/2.70  cnf(c_0_87, negated_conjecture, (~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_84]), c_0_29]), c_0_34])])).
% 2.52/2.70  cnf(c_0_88, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 2.52/2.70  cnf(c_0_89, negated_conjecture, (~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 2.52/2.70  cnf(c_0_90, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_41]), c_0_29])])).
% 2.52/2.70  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_12]), c_0_37])]), ['proof']).
% 2.52/2.70  # SZS output end CNFRefutation
% 2.52/2.70  # Proof object total steps             : 92
% 2.52/2.70  # Proof object clause steps            : 75
% 2.52/2.70  # Proof object formula steps           : 17
% 2.52/2.70  # Proof object conjectures             : 62
% 2.52/2.70  # Proof object clause conjectures      : 59
% 2.52/2.70  # Proof object formula conjectures     : 3
% 2.52/2.70  # Proof object initial clauses used    : 21
% 2.52/2.70  # Proof object initial formulas used   : 8
% 2.52/2.70  # Proof object generating inferences   : 53
% 2.52/2.70  # Proof object simplifying inferences  : 62
% 2.52/2.70  # Training examples: 0 positive, 0 negative
% 2.52/2.70  # Parsed axioms                        : 8
% 2.52/2.70  # Removed by relevancy pruning/SinE    : 0
% 2.52/2.70  # Initial clauses                      : 21
% 2.52/2.70  # Removed in clause preprocessing      : 0
% 2.52/2.70  # Initial clauses in saturation        : 21
% 2.52/2.70  # Processed clauses                    : 10515
% 2.52/2.70  # ...of these trivial                  : 51
% 2.52/2.70  # ...subsumed                          : 8314
% 2.52/2.70  # ...remaining for further processing  : 2150
% 2.52/2.70  # Other redundant clauses eliminated   : 0
% 2.52/2.70  # Clauses deleted for lack of memory   : 0
% 2.52/2.70  # Backward-subsumed                    : 285
% 2.52/2.70  # Backward-rewritten                   : 59
% 2.52/2.70  # Generated clauses                    : 186165
% 2.52/2.70  # ...of the previous two non-trivial   : 180927
% 2.52/2.70  # Contextual simplify-reflections      : 188
% 2.52/2.70  # Paramodulations                      : 186152
% 2.52/2.70  # Factorizations                       : 0
% 2.52/2.70  # Equation resolutions                 : 0
% 2.52/2.70  # Propositional unsat checks           : 0
% 2.52/2.70  #    Propositional check models        : 0
% 2.52/2.70  #    Propositional check unsatisfiable : 0
% 2.52/2.70  #    Propositional clauses             : 0
% 2.52/2.70  #    Propositional clauses after purity: 0
% 2.52/2.70  #    Propositional unsat core size     : 0
% 2.52/2.70  #    Propositional preprocessing time  : 0.000
% 2.52/2.70  #    Propositional encoding time       : 0.000
% 2.52/2.70  #    Propositional solver time         : 0.000
% 2.52/2.70  #    Success case prop preproc time    : 0.000
% 2.52/2.70  #    Success case prop encoding time   : 0.000
% 2.52/2.70  #    Success case prop solver time     : 0.000
% 2.52/2.70  # Current number of processed clauses  : 1779
% 2.52/2.70  #    Positive orientable unit clauses  : 74
% 2.52/2.70  #    Positive unorientable unit clauses: 0
% 2.52/2.70  #    Negative unit clauses             : 4
% 2.52/2.70  #    Non-unit-clauses                  : 1701
% 2.52/2.70  # Current number of unprocessed clauses: 170030
% 2.52/2.70  # ...number of literals in the above   : 1336886
% 2.52/2.70  # Current number of archived formulas  : 0
% 2.52/2.70  # Current number of archived clauses   : 365
% 2.52/2.70  # Clause-clause subsumption calls (NU) : 2089028
% 2.52/2.70  # Rec. Clause-clause subsumption calls : 308178
% 2.52/2.70  # Non-unit clause-clause subsumptions  : 8313
% 2.52/2.70  # Unit Clause-clause subsumption calls : 2762
% 2.52/2.70  # Rewrite failures with RHS unbound    : 0
% 2.52/2.70  # BW rewrite match attempts            : 380
% 2.52/2.70  # BW rewrite match successes           : 10
% 2.52/2.70  # Condensation attempts                : 0
% 2.52/2.70  # Condensation successes               : 0
% 2.52/2.70  # Termbank termtop insertions          : 5014208
% 2.52/2.70  
% 2.52/2.70  # -------------------------------------------------
% 2.52/2.70  # User time                : 2.280 s
% 2.52/2.70  # System time              : 0.072 s
% 2.52/2.70  # Total time               : 2.353 s
% 2.52/2.70  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
