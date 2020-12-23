%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:07 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 603 expanded)
%              Number of clauses        :   73 ( 249 expanded)
%              Number of leaves         :    6 ( 140 expanded)
%              Depth                    :    7
%              Number of atoms          :  385 (3614 expanded)
%              Number of equality atoms :   23 ( 157 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_pre_topc])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X14,X16] :
      ( ( r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X12,u1_pre_topc(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X12),u1_pre_topc(X10))
        | ~ r2_hidden(X12,u1_pre_topc(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( X12 = k9_subset_1(u1_struct_0(X11),esk1_3(X10,X11,X12),k2_struct_0(X11))
        | ~ r2_hidden(X12,u1_pre_topc(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X14,u1_pre_topc(X10))
        | X12 != k9_subset_1(u1_struct_0(X11),X14,k2_struct_0(X11))
        | r2_hidden(X12,u1_pre_topc(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_2(X10,X11),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X16,u1_pre_topc(X10))
        | esk2_2(X10,X11) != k9_subset_1(u1_struct_0(X11),X16,k2_struct_0(X11))
        | ~ r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk3_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))
        | ~ r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk3_2(X10,X11),u1_pre_topc(X10))
        | r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))
        | ~ r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( esk2_2(X10,X11) = k9_subset_1(u1_struct_0(X11),esk3_2(X10,X11),k2_struct_0(X11))
        | r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))
        | ~ r1_tarski(k2_struct_0(X11),k2_struct_0(X10))
        | m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_10,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_16,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_10]),
    [final]).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_13,c_0_10])]),
    [final]).

cnf(c_0_22,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_26,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_27,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_16,c_0_10]),
    [final]).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_17,c_0_10]),
    [final]).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_18,c_0_10]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11]),
    [final]).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_35,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0)) = esk2_2(X1,esk4_0)
    | r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0)) = esk2_2(X1,esk5_0)
    | r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,X1)
    | m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))
    | m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,X1)
    | m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))
    | m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | esk2_2(X1,esk4_0) != k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))
    | ~ r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | esk2_2(X1,esk5_0) != k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))
    | ~ r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_11]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_11]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_11]),
    [final]).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_15]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_54,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_15]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk4_0,esk4_0)
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_11]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk5_0,esk4_0)
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0)) = esk2_2(esk5_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_11]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_11]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk4_0,esk4_0)
    | ~ r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_11]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk5_0,esk4_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk2_2(esk5_0,esk5_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0)) = X1
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_15]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_15]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_15]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_23]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_11]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_23]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k2_struct_0(esk4_0))
    | ~ r1_tarski(X1,k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk5_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_52]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_23]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_23]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.14/0.38  # and selection function HSelectMinInfpos.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t39_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.14/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.38  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.14/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t39_pre_topc])).
% 0.14/0.38  fof(c_0_7, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_pre_topc(esk5_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X10, X11, X12, X14, X16]:(((r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|~m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))&((((m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))|~r2_hidden(X12,u1_pre_topc(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))&(r2_hidden(esk1_3(X10,X11,X12),u1_pre_topc(X10))|~r2_hidden(X12,u1_pre_topc(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(X12=k9_subset_1(u1_struct_0(X11),esk1_3(X10,X11,X12),k2_struct_0(X11))|~r2_hidden(X12,u1_pre_topc(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|~r2_hidden(X14,u1_pre_topc(X10))|X12!=k9_subset_1(u1_struct_0(X11),X14,k2_struct_0(X11))|r2_hidden(X12,u1_pre_topc(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))))&((m1_subset_1(esk2_2(X10,X11),k1_zfmisc_1(u1_struct_0(X11)))|~r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))&((~r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X10)))|~r2_hidden(X16,u1_pre_topc(X10))|esk2_2(X10,X11)!=k9_subset_1(u1_struct_0(X11),X16,k2_struct_0(X11)))|~r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))&(((m1_subset_1(esk3_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))|r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))|~r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10))&(r2_hidden(esk3_2(X10,X11),u1_pre_topc(X10))|r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))|~r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(esk2_2(X10,X11)=k9_subset_1(u1_struct_0(X11),esk3_2(X10,X11),k2_struct_0(X11))|r2_hidden(esk2_2(X10,X11),u1_pre_topc(X11))|~r1_tarski(k2_struct_0(X11),k2_struct_0(X10))|m1_pre_topc(X11,X10)|~l1_pre_topc(X11)|~l1_pre_topc(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_12, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(X3,u1_pre_topc(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|X3!=k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X4)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_16, plain, (X1=k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_18, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_19, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_12, c_0_10]), ['final']).
% 0.14/0.38  fof(c_0_20, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(X3))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_13, c_0_10])]), ['final']).
% 0.14/0.38  cnf(c_0_22, plain, (esk2_2(X1,X2)=k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_26, plain, (m1_pre_topc(X2,X1)|~r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X1))|esk2_2(X1,X2)!=k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_27, plain, (k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1))=X3|~r2_hidden(X3,u1_pre_topc(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_16, c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_17, c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_29, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_18, c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_30, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  fof(c_0_31, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  fof(c_0_35, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(esk4_0))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_21, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0))=esk2_2(X1,esk4_0)|r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_22, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0))=esk2_2(X1,esk5_0)|r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,X1)|m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))|m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_25, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,X1)|m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))|m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_25, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk4_0,X1)|esk2_2(X1,esk4_0)!=k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))|~r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk5_0,X1)|esk2_2(X1,esk5_0)!=k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))|~r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1))=X2|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk5_0,X1)|m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk4_0,X1)|m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_50, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.14/0.38  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_54, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_36, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk4_0,esk4_0)|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(esk5_0))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_21, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk5_0,esk4_0)|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0))=esk2_2(esk5_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_41, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk4_0,esk4_0)|~r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk5_0,esk4_0)|~r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0))!=esk2_2(esk5_0,esk5_0)|~r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0))=X1|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_45, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1))=X2|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_46, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_47, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_75, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_76, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,k2_struct_0(esk4_0))|~r1_tarski(X1,k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.14/0.38  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk5_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_52]), ['final']).
% 0.14/0.38  cnf(c_0_81, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_82, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_83, negated_conjecture, (m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_53, c_0_51]), ['final']).
% 0.14/0.38  cnf(c_0_84, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_85, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_11]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 86
% 0.14/0.38  # Proof object clause steps            : 73
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 56
% 0.14/0.38  # Proof object clause conjectures      : 53
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 19
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 49
% 0.14/0.38  # Proof object simplifying inferences  : 6
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 19
% 0.14/0.38  # Processed clauses                    : 88
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 88
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 57
% 0.14/0.38  # ...of the previous two non-trivial   : 50
% 0.14/0.38  # Contextual simplify-reflections      : 5
% 0.14/0.38  # Paramodulations                      : 56
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 68
% 0.14/0.38  #    Positive orientable unit clauses  : 9
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 58
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 19
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1732
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 361
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 31
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4177
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.037 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.039 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
