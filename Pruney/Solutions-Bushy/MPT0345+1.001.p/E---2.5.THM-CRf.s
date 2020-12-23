%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0345+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   81 (6704 expanded)
%              Number of clauses        :   68 (2692 expanded)
%              Number of leaves         :    6 (1531 expanded)
%              Depth                    :   25
%              Number of atoms          :  253 (39459 expanded)
%              Number of equality atoms :   25 (4566 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        | r2_hidden(X5,X4) ) ) )
               => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          | r2_hidden(X5,X4) ) ) )
                 => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_subset_1])).

fof(c_0_7,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k4_subset_1(X22,X23,X24) = k2_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X33] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( ~ r2_hidden(X33,esk4_0)
        | r2_hidden(X33,esk5_0)
        | r2_hidden(X33,esk6_0)
        | ~ m1_subset_1(X33,esk3_0) )
      & ( ~ r2_hidden(X33,esk5_0)
        | r2_hidden(X33,esk4_0)
        | ~ m1_subset_1(X33,esk3_0) )
      & ( ~ r2_hidden(X33,esk6_0)
        | r2_hidden(X33,esk4_0)
        | ~ m1_subset_1(X33,esk3_0) )
      & esk4_0 != k4_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_9,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | m1_subset_1(k4_subset_1(X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_12,negated_conjecture,
    ( k4_subset_1(esk3_0,X1,esk6_0) = k2_xboole_0(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ( m1_subset_1(esk2_3(X25,X26,X27),X25)
        | r1_tarski(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X26)
        | r1_tarski(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) )
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | r1_tarski(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k4_subset_1(esk3_0,esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10]),c_0_13])])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,X1,esk4_0),esk3_0)
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 != k4_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,k2_xboole_0(esk5_0,esk6_0)),X1)
    | r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk3_0)
    | r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

fof(c_0_28,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,esk4_0),X1)
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk3_0)
    | ~ r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | ~ r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_29]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0))
    | r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,X1,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_36,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk3_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,X1,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | ~ r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_42]),c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | m1_subset_1(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_58]),c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,X1,k2_xboole_0(esk5_0,esk6_0)),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_18])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk3_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_66]),c_0_52])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_71])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk6_0)
    | r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_71]),c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_78])]),c_0_79]),
    [proof]).

%------------------------------------------------------------------------------
