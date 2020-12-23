%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:19 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 596 expanded)
%              Number of clauses        :   75 ( 244 expanded)
%              Number of leaves         :    7 ( 139 expanded)
%              Depth                    :    7
%              Number of atoms          :  401 (3977 expanded)
%              Number of equality atoms :   23 ( 152 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_pre_topc,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_pre_topc])).

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
    ( ~ v2_struct_0(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

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

cnf(c_0_15,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_18,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_23,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_15,c_0_12])]),
    [final]).

cnf(c_0_24,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
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
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_27,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_18,c_0_12]),
    [final]).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_20,c_0_12]),
    [final]).

cnf(c_0_32,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X5,X6)
      | v1_xboole_0(X6)
      | r2_hidden(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17]),
    [final]).

fof(c_0_36,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r2_hidden(X2,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0)) = esk2_2(X1,esk4_0)
    | m1_pre_topc(esk4_0,X1)
    | r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0)) = esk2_2(X1,esk5_0)
    | m1_pre_topc(esk5_0,X1)
    | r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | esk2_2(X1,esk4_0) != k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))
    | ~ r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | esk2_2(X1,esk5_0) != k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))
    | ~ r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))
    | m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_13]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13]),
    [final]).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_54,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_55,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_17]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk4_0,esk4_0)
    | m1_pre_topc(esk4_0,esk4_0)
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0)) = esk2_2(esk5_0,esk4_0)
    | m1_pre_topc(esk4_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0)) = esk2_2(esk5_0,esk5_0)
    | m1_pre_topc(esk5_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk4_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))
    | ~ r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_13]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk2_2(esk5_0,esk4_0)
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))
    | ~ r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0)) = X1
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_17]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk2_2(esk5_0,esk5_0)
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))
    | ~ r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_13]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_13]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))
    | m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_25]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_25]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_17]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_17]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0)
    | m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_13]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_25]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_53]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_25]),
    [final]).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_25]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_13]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.13/0.38  # and selection function HSelectMinInfpos.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t55_pre_topc, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.13/0.38  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t55_pre_topc])).
% 0.13/0.38  fof(c_0_8, plain, ![X12, X13, X14, X16, X18]:(((r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&((((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(r2_hidden(esk1_3(X12,X13,X14),u1_pre_topc(X12))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(X14=k9_subset_1(u1_struct_0(X13),esk1_3(X12,X13,X14),k2_struct_0(X13))|~r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X16,u1_pre_topc(X12))|X14!=k9_subset_1(u1_struct_0(X13),X16,k2_struct_0(X13))|r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X13)))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&((~r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X18,u1_pre_topc(X12))|esk2_2(X12,X13)!=k9_subset_1(u1_struct_0(X13),X18,k2_struct_0(X13)))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(((m1_subset_1(esk3_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12))&(r2_hidden(esk3_2(X12,X13),u1_pre_topc(X12))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))&(esk2_2(X12,X13)=k9_subset_1(u1_struct_0(X13),esk3_2(X12,X13),k2_struct_0(X13))|r2_hidden(esk2_2(X12,X13),u1_pre_topc(X13))|~r1_tarski(k2_struct_0(X13),k2_struct_0(X12))|m1_pre_topc(X13,X12)|~l1_pre_topc(X13)|~l1_pre_topc(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.13/0.38  fof(c_0_9, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&~m1_subset_1(esk6_0,u1_struct_0(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.38  cnf(c_0_11, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_12, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_14, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_15, plain, (r2_hidden(X3,u1_pre_topc(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|X3!=k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X4)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_18, plain, (X1=k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_20, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_21, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~r2_hidden(X2,u1_pre_topc(X3))|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_15, c_0_12])]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (esk2_2(X1,X2)=k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (m1_pre_topc(X2,X1)|~r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X1))|esk2_2(X1,X2)!=k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1))=X3|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,u1_pre_topc(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_18, c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_20, c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_32, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  fof(c_0_33, plain, ![X5, X6]:(~m1_subset_1(X5,X6)|(v1_xboole_0(X6)|r2_hidden(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_17]), ['final']).
% 0.13/0.38  fof(c_0_36, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~r2_hidden(X2,u1_pre_topc(esk4_0))|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_23, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(X1,esk4_0),k2_struct_0(esk4_0))=esk2_2(X1,esk4_0)|m1_pre_topc(esk4_0,X1)|r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(X1,esk5_0),k2_struct_0(esk5_0))=esk2_2(X1,esk5_0)|m1_pre_topc(esk5_0,X1)|r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk4_0,X1)|esk2_2(X1,esk4_0)!=k9_subset_1(u1_struct_0(esk4_0),X2,k2_struct_0(esk4_0))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))|~r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk4_0,X1,X2),k2_struct_0(X1))=X2|~m1_pre_topc(X1,esk4_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk5_0,X1)|esk2_2(X1,esk5_0)!=k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk5_0))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))|~r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk4_0,X1)|r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk3_2(X1,esk4_0),u1_pre_topc(X1))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_28, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk4_0,X1)|r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk4_0))|m1_subset_1(esk3_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk5_0,X1)|r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|m1_subset_1(esk3_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk5_0,X1)|r2_hidden(esk2_2(X1,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk3_2(X1,esk5_0),u1_pre_topc(X1))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_28, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk4_0))|~m1_pre_topc(X1,esk4_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_pre_topc(X1,esk4_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk4_0,X1)|m1_subset_1(esk2_2(X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_50, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk5_0,X1)|m1_subset_1(esk2_2(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~l1_pre_topc(X1)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  fof(c_0_54, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  cnf(c_0_55, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_37, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk4_0,esk4_0)|m1_pre_topc(esk4_0,esk4_0)|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_2(esk5_0,esk4_0),k2_struct_0(esk4_0))=esk2_2(esk5_0,esk4_0)|m1_pre_topc(esk4_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk5_0,esk5_0),k2_struct_0(esk5_0))=esk2_2(esk5_0,esk5_0)|m1_pre_topc(esk5_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~m1_pre_topc(X1,esk5_0)|~r2_hidden(X2,u1_pre_topc(esk5_0))|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_23, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk4_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))|~r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_40, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk2_2(esk5_0,esk4_0)|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))|~r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_40, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,X1),k2_struct_0(esk5_0))=X1|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_41, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0))!=esk2_2(esk5_0,esk5_0)|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))|~r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_42, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|r2_hidden(esk3_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|r2_hidden(esk3_2(esk5_0,esk4_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|r2_hidden(esk2_2(esk4_0,esk4_0),u1_pre_topc(esk4_0))|m1_subset_1(esk3_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k9_subset_1(u1_struct_0(X1),esk1_3(esk5_0,X1,X2),k2_struct_0(X1))=X2|~m1_pre_topc(X1,esk5_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk4_0),u1_pre_topc(esk4_0))|m1_subset_1(esk3_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|m1_subset_1(esk3_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|r2_hidden(esk3_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|r2_hidden(esk2_2(esk5_0,esk5_0),u1_pre_topc(esk5_0))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk5_0,X1),u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_47, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_3(esk5_0,X1,X2),u1_pre_topc(esk5_0))|~m1_pre_topc(X1,esk5_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_pre_topc(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_48, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_pre_topc(X1,esk5_0)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)|m1_subset_1(esk2_2(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (r2_hidden(k2_struct_0(esk5_0),k1_zfmisc_1(k2_struct_0(esk4_0)))|v1_xboole_0(k1_zfmisc_1(k2_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_struct_0(X1),k2_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_53]), ['final']).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_83, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_54]), ['final']).
% 0.13/0.38  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (~m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_13]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 90
% 0.13/0.38  # Proof object clause steps            : 75
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 57
% 0.13/0.38  # Proof object clause conjectures      : 54
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 48
% 0.13/0.38  # Proof object simplifying inferences  : 6
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 93
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 93
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 55
% 0.13/0.38  # ...of the previous two non-trivial   : 49
% 0.13/0.38  # Contextual simplify-reflections      : 5
% 0.13/0.38  # Paramodulations                      : 54
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 70
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 59
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1457
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 369
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 8
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4317
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
