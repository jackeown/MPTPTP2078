%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1366+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:11 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 944 expanded)
%              Number of clauses        :   42 ( 293 expanded)
%              Number of leaves         :    4 ( 234 expanded)
%              Depth                    :   11
%              Number of atoms          :  400 (9001 expanded)
%              Number of equality atoms :   41 ( 413 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :  106 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ( v8_pre_topc(X1)
          & v1_compts_1(X1) )
       => v9_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_compts_1)).

fof(d5_compts_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v9_pre_topc(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X3 != k1_xboole_0
                    & v4_pre_topc(X3,X1)
                    & r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X3))
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ~ ( v3_pre_topc(X4,X1)
                                & v3_pre_topc(X5,X1)
                                & r2_hidden(X2,X4)
                                & r1_tarski(X3,X5)
                                & r1_xboole_0(X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_compts_1)).

fof(t17_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_compts_1(X1)
              & v4_pre_topc(X2,X1) )
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(t15_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v8_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_compts_1(X2,X1)
             => ( X2 = k1_xboole_0
                | ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
                        & ! [X4] :
                            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                               => ~ ( v3_pre_topc(X4,X1)
                                    & v3_pre_topc(X5,X1)
                                    & r2_hidden(X3,X4)
                                    & r1_tarski(X2,X5)
                                    & r1_xboole_0(X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_compts_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( ( v8_pre_topc(X1)
            & v1_compts_1(X1) )
         => v9_pre_topc(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t21_compts_1])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & v8_pre_topc(esk7_0)
    & v1_compts_1(esk7_0)
    & ~ v9_pre_topc(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X13,X14] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk1_3(X6,X7,X8),X6)
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk2_3(X6,X7,X8),X6)
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X7,esk1_3(X6,X7,X8))
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r1_tarski(X8,esk2_3(X6,X7,X8))
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8))
        | X8 = k1_xboole_0
        | ~ v4_pre_topc(X8,X6)
        | ~ r2_hidden(X7,k3_subset_1(u1_struct_0(X6),X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_1(X6),u1_struct_0(X6))
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk4_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( esk4_1(X6) != k1_xboole_0
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v4_pre_topc(esk4_1(X6),X6)
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_1(X6),k3_subset_1(u1_struct_0(X6),esk4_1(X6)))
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X13,X6)
        | ~ v3_pre_topc(X14,X6)
        | ~ r2_hidden(esk3_1(X6),X13)
        | ~ r1_tarski(esk4_1(X6),X14)
        | ~ r1_xboole_0(X13,X14)
        | v9_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_compts_1])])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ v1_compts_1(X20)
      | ~ v4_pre_topc(X21,X20)
      | v2_compts_1(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ v9_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v9_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ( m1_subset_1(esk5_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk6_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v3_pre_topc(esk5_3(X15,X16,X17),X15)
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v3_pre_topc(esk6_3(X15,X16,X17),X15)
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(X17,esk5_3(X15,X16,X17))
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(X16,esk6_3(X15,X16,X17))
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_xboole_0(esk5_3(X15,X16,X17),esk6_3(X15,X16,X17))
        | ~ r2_hidden(X17,k3_subset_1(u1_struct_0(X15),X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 = k1_xboole_0
        | ~ v2_compts_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v8_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_compts_1])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v9_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_14]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v8_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( v2_compts_1(esk4_1(esk7_0),esk7_0)
    | ~ v4_pre_topc(esk4_1(esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_10])])).

cnf(c_0_22,plain,
    ( v4_pre_topc(esk4_1(X1),X1)
    | v9_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_1(X1),k3_subset_1(u1_struct_0(X1),esk4_1(X1)))
    | v9_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( v3_pre_topc(esk6_3(X1,X2,X3),X1)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,esk6_3(X2,X1,X3))
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X2),X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v8_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk6_3(esk7_0,X1,esk3_1(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_27,negated_conjecture,
    ( v2_compts_1(esk4_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_10]),c_0_11])]),c_0_8]),c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),esk4_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_23]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k1_xboole_0
    | v3_pre_topc(esk6_3(esk7_0,X1,esk3_1(esk7_0)),esk7_0)
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_tarski(X1,esk6_3(esk7_0,X1,esk3_1(esk7_0)))
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X2),X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_compts_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v8_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( v3_pre_topc(esk5_3(X1,X2,X3),X1)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( v9_pre_topc(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | ~ r2_hidden(esk3_1(X2),X1)
    | ~ r1_tarski(esk4_1(X2),X3)
    | ~ r1_xboole_0(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | m1_subset_1(esk6_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | v3_pre_topc(esk6_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | r1_tarski(esk4_1(esk7_0),esk6_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk5_3(esk7_0,X1,esk3_1(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),esk5_3(esk7_0,X1,esk3_1(esk7_0)))
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_xboole_0
    | v3_pre_topc(esk5_3(esk7_0,X1,esk3_1(esk7_0)),esk7_0)
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3))
    | X2 = k1_xboole_0
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk6_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)))
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_10]),c_0_11])]),c_0_8]),c_0_12]),c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | m1_subset_1(esk5_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),esk5_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | v3_pre_topc(esk5_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_27]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_xboole_0(esk5_3(esk7_0,X1,esk3_1(esk7_0)),esk6_3(esk7_0,X1,esk3_1(esk7_0)))
    | ~ v2_compts_1(X1,esk7_0)
    | ~ r2_hidden(esk3_1(esk7_0),k3_subset_1(u1_struct_0(esk7_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_47,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0
    | ~ r1_xboole_0(esk5_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0)),esk6_3(esk7_0,esk4_1(esk7_0),esk3_1(esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( v9_pre_topc(X1)
    | v2_struct_0(X1)
    | esk4_1(X1) != k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_49,negated_conjecture,
    ( esk4_1(esk7_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_16]),c_0_27]),c_0_28])]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_10]),c_0_11])]),c_0_8]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
