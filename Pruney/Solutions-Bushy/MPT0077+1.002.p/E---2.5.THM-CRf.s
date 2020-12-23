%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0077+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:59 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 164 expanded)
%              Number of clauses        :   29 (  80 expanded)
%              Number of leaves         :    3 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 866 expanded)
%              Number of equality atoms :   10 (  56 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

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

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_4,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk5_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | r1_xboole_0(esk3_0,X1)
    | ~ r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,X1)
    | ~ r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,k2_xboole_0(X2,X3)),X2)
    | r2_hidden(esk2_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0)
    | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(X1,k2_xboole_0(X2,esk5_0))
    | r2_hidden(esk2_2(X1,k2_xboole_0(X2,esk5_0)),X2)
    | ~ r2_hidden(esk2_2(X1,k2_xboole_0(X2,esk5_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk5_0))
    | r2_hidden(esk2_2(esk3_0,k2_xboole_0(X1,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_33]),
    [proof]).

%------------------------------------------------------------------------------
