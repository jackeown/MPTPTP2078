%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:07 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 611 expanded)
%              Number of clauses        :   76 ( 253 expanded)
%              Number of leaves         :    7 ( 142 expanded)
%              Depth                    :    7
%              Number of atoms          :  390 (3622 expanded)
%              Number of equality atoms :   28 ( 165 expanded)
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_pre_topc])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X16,X18] :
      ( ( r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk1_3(X12,X13,X14),u1_pre_topc(X12))
        | ~ r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( X14 = k9_subset_1(u1_struct_0(X13),esk1_3(X12,X13,X14),k2_struct_0(X13))
        | ~ r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X16,u1_pre_topc(X12))
        | X14 != k9_subset_1(u1_struct_0(X13),X16,k2_struct_0(X13))
        | r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X18,u1_pre_topc(X12))
        | esk2_2(X12,X13) != k9_subset_1(u1_struct_0(X13),X18,k2_struct_0(X13))
        | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))
        | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_2(X12,X13),u1_pre_topc(X12))
        | r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))
        | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( esk2_2(X12,X13) = k9_subset_1(u1_struct_0(X13),esk3_2(X12,X13),k2_struct_0(X13))
        | r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))
        | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(X12))
        | m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_9,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12]),
    [final]).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_26,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_16,c_0_12])]),
    [final]).

cnf(c_0_27,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_30,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_31,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_32,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_20,c_0_12]),
    [final]).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_21,c_0_12]),
    [final]).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_36,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(k2_xboole_0(X5,X6),X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

fof(c_0_40,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0)) = esk2_2(X1,esk4_0)
    | r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0)) = esk2_2(X1,esk5_0)
    | r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))
    | m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_13]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | esk2_2(X1,esk4_0) != k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))
    | ~ r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | esk2_2(X1,esk5_0) != k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))
    | ~ r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))
    | m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,X1)
    | m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,X1)
    | m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_13]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_13]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_13]),
    [final]).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) = k2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(esk6_0,u1_struct_0(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_39]),
    [final]).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk4_0,esk4_0)
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_13]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk5_0,esk4_0)
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0)) = esk2_2(esk5_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_28]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_13]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk4_0,esk4_0)
    | ~ r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_13]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk5_0,esk4_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk2_2(esk5_0,esk5_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0)) = X1
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_18]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_13]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_pre_topc(esk4_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_pre_topc(esk5_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_28]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_18]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_18]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_13]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_28]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_28]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(u1_struct_0(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_28]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_28]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_13]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:12:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.18/0.36  # and selection function HSelectMinInfpos.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # No proof found!
% 0.18/0.36  # SZS status CounterSatisfiable
% 0.18/0.36  # SZS output start Saturation
% 0.18/0.36  fof(t39_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.18/0.36  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.18/0.36  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.36  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t39_pre_topc])).
% 0.18/0.36  fof(c_0_8, plain, ![X12, X13, X14, X16, X18]:(((r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&((((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(r2_hidden(esk1_3(X12,X13,X14),u1_pre_topc(X12))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(X14=k9_subset_1(u1_struct_0(X13),esk1_3(X12,X13,X14),k2_struct_0(X13))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X16,u1_pre_topc(X12))|X14!=k9_subset_1(u1_struct_0(X13),X16,k2_struct_0(X13))|r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X13)))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&((~r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X18,u1_pre_topc(X12))|esk2_2(X12,X13)!=k9_subset_1(u1_struct_0(X13),X18,k2_struct_0(X13)))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(((m1_subset_1(esk3_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(r2_hidden(esk3_2(X12,X13),u1_pre_topc(X12))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(esk2_2(X12,X13)=k9_subset_1(u1_struct_0(X13),esk3_2(X12,X13),k2_struct_0(X13))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.18/0.36  fof(c_0_9, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.36  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_pre_topc(esk5_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.18/0.36  cnf(c_0_11, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_12, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_14, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.18/0.36  fof(c_0_15, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.36  cnf(c_0_16, plain, (r2_hidden(X3,u1_pre_topc(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|X3!=k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X4)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_19, plain, (X1=k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  fof(c_0_22, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_26, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(X3))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_16, c_0_12])]), ['final']).
% 0.18/0.36  cnf(c_0_27, plain, (esk2_2(X1,X2)=k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_29, plain, (r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_30, plain, (m1_pre_topc(X2,X1)|~r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X1))|esk2_2(X1,X2)!=k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_31, plain, (k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1))=X3|~r2_hidden(X3,u1_pre_topc(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.18/0.36  cnf(c_0_32, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_20, c_0_12]), ['final']).
% 0.18/0.36  cnf(c_0_34, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_21, c_0_12]), ['final']).
% 0.18/0.36  cnf(c_0_35, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  fof(c_0_36, plain, ![X5, X6, X7]:(~r1_tarski(k2_xboole_0(X5,X6),X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.36  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.18/0.36  fof(c_0_40, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(esk4_0))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_26, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0))=esk2_2(X1,esk4_0)|r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0))=esk2_2(X1,esk5_0)|r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))|m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk4_0,X1)|esk2_2(X1,esk4_0)!=k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))|~r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk5_0,X1)|esk2_2(X1,esk5_0)!=k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))|~r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1))=X2|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))|m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,X1)|m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,X1)|m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk5_0,X1)|m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_35, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_54, negated_conjecture, (m1_pre_topc(esk4_0,X1)|m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_35, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_55, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.18/0.36  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k2_struct_0(esk5_0),k2_struct_0(esk4_0))=k2_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38]), ['final']).
% 0.18/0.36  cnf(c_0_57, negated_conjecture, (k2_xboole_0(esk6_0,u1_struct_0(esk5_0))=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_39]), ['final']).
% 0.18/0.36  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_59, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.18/0.36  cnf(c_0_60, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_61, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk4_0,esk4_0)|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_62, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk5_0,esk4_0)|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0))=esk2_2(esk5_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_64, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(esk5_0))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_26, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk4_0,esk4_0)|~r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk5_0,esk4_0)|~r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0))!=esk2_2(esk5_0,esk5_0)|~r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_70, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0))=X1|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_47, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_72, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1))=X2|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_73, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_pre_topc(esk4_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_pre_topc(esk5_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_51, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_52, c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_80, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_81, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_82, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),X1)|~r1_tarski(k2_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.18/0.36  cnf(c_0_84, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_85, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(u1_struct_0(esk5_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_57]), ['final']).
% 0.18/0.36  cnf(c_0_86, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_87, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_58, c_0_38]), ['final']).
% 0.18/0.36  cnf(c_0_89, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_90, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_13]), ['final']).
% 0.18/0.36  # SZS output end Saturation
% 0.18/0.36  # Proof object total steps             : 91
% 0.18/0.36  # Proof object clause steps            : 76
% 0.18/0.36  # Proof object formula steps           : 15
% 0.18/0.36  # Proof object conjectures             : 58
% 0.18/0.36  # Proof object clause conjectures      : 55
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 20
% 0.18/0.36  # Proof object initial formulas used   : 7
% 0.18/0.36  # Proof object generating inferences   : 51
% 0.18/0.36  # Proof object simplifying inferences  : 6
% 0.18/0.36  # Parsed axioms                        : 7
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 20
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 20
% 0.18/0.36  # Processed clauses                    : 92
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 92
% 0.18/0.36  # Other redundant clauses eliminated   : 1
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 0
% 0.18/0.36  # Generated clauses                    : 59
% 0.18/0.36  # ...of the previous two non-trivial   : 52
% 0.18/0.36  # Contextual simplify-reflections      : 5
% 0.18/0.36  # Paramodulations                      : 58
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 1
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 71
% 0.18/0.36  #    Positive orientable unit clauses  : 11
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 59
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 20
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 2493
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 502
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 5
% 0.18/0.36  # Unit Clause-clause subsumption calls : 32
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 0
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 4254
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.032 s
% 0.18/0.36  # System time              : 0.005 s
% 0.18/0.36  # Total time               : 0.038 s
% 0.18/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
