%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0363+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:30 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 315 expanded)
%              Number of clauses        :   68 ( 155 expanded)
%              Number of leaves         :    6 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 (1463 expanded)
%              Number of equality atoms :   25 ( 201 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,X3)
            <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_subset_1])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,X12) = k4_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_xboole_0(esk5_0,esk6_0)
      | ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk6_0)) )
    & ( r1_xboole_0(esk5_0,esk6_0)
      | r1_tarski(esk5_0,k3_subset_1(esk4_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X25,X26,X28,X29,X30] :
      ( ( r2_hidden(esk3_2(X25,X26),X25)
        | r1_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | r1_xboole_0(X25,X26) )
      & ( ~ r2_hidden(X30,X28)
        | ~ r2_hidden(X30,X29)
        | ~ r1_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_11,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0)
    | r1_tarski(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( k3_subset_1(esk4_0,esk6_0) = k4_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0)
    | r1_tarski(esk5_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0)
    | r1_xboole_0(X1,esk5_0)
    | r2_hidden(esk3_2(X1,esk5_0),k4_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0)
    | r1_xboole_0(X1,esk5_0)
    | ~ r2_hidden(esk3_2(X1,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0)
    | r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0)
    | ~ r2_hidden(esk3_2(X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk3_2(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(X2,esk4_0))
    | ~ r2_hidden(esk3_2(X1,k4_xboole_0(X2,esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | r2_hidden(esk3_2(X1,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k4_xboole_0(X2,esk4_0)
    | r2_hidden(esk2_3(X2,esk4_0,X1),X1)
    | ~ r2_hidden(esk2_3(X2,esk4_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,X2))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk3_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | r2_hidden(esk3_2(X1,esk5_0),k4_xboole_0(esk4_0,X2))
    | r2_hidden(esk3_2(X1,esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k4_xboole_0(esk6_0,esk4_0)
    | r2_hidden(esk2_3(esk6_0,esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,X1),X2)
    | ~ r2_hidden(esk3_2(k4_xboole_0(esk5_0,X1),X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk4_0,X2)),esk5_0)
    | r2_hidden(esk3_2(k4_xboole_0(X1,k4_xboole_0(esk4_0,X2)),esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk6_0,esk4_0)
    | ~ r2_hidden(esk2_3(esk6_0,esk4_0,k4_xboole_0(esk5_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(esk5_0,esk6_0)
    | ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_64]),c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_65]),c_0_66])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_xboole_0(esk5_0,esk6_0)
    | ~ r1_tarski(esk5_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk6_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79]),
    [proof]).

%------------------------------------------------------------------------------
