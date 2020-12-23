%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1110+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of clauses        :   26 (  32 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 252 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8,X10,X12] :
      ( ( r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),u1_pre_topc(X6))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( X8 = k9_subset_1(u1_struct_0(X7),esk1_3(X6,X7,X8),k2_struct_0(X7))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X10,u1_pre_topc(X6))
        | X8 != k9_subset_1(u1_struct_0(X7),X10,k2_struct_0(X7))
        | r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X12,u1_pre_topc(X6))
        | esk2_2(X6,X7) != k9_subset_1(u1_struct_0(X7),X12,k2_struct_0(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_2(X6,X7),u1_pre_topc(X6))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( esk2_2(X6,X7) = k9_subset_1(u1_struct_0(X7),esk3_2(X6,X7),k2_struct_0(X7))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_11,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_11])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | k2_struct_0(X5) = u1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk5_0) = k2_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,k2_struct_0(esk4_0))
    | ~ r1_tarski(X1,k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,k2_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk4_0) = k2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk6_0,k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).

%------------------------------------------------------------------------------
