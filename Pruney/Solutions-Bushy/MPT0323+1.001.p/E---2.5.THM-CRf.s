%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0323+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:25 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   83 (52155 expanded)
%              Number of clauses        :   74 (21956 expanded)
%              Number of leaves         :    4 (12837 expanded)
%              Depth                    :   34
%              Number of atoms          :  334 (660042 expanded)
%              Number of equality atoms :    7 ( 450 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   72 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t136_zfmisc_1,conjecture,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(k1_zfmisc_1(X3),X2) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(t9_tarski,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ~ ( r2_hidden(X3,X2)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) ) ) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
      ? [X2] :
        ( r2_hidden(X1,X2)
        & ! [X3,X4] :
            ( ( r2_hidden(X3,X2)
              & r1_tarski(X4,X3) )
           => r2_hidden(X4,X2) )
        & ! [X3] :
            ( r2_hidden(X3,X2)
           => r2_hidden(k1_zfmisc_1(X3),X2) )
        & ! [X3] :
            ~ ( r1_tarski(X3,X2)
              & ~ r2_tarski(X3,X2)
              & ~ r2_hidden(X3,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t136_zfmisc_1])).

fof(c_0_5,negated_conjecture,(
    ! [X28] :
      ( ( r1_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( r1_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r2_hidden(esk6_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( r1_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( r1_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | r1_tarski(esk7_1(X28),esk6_1(X28))
        | ~ r2_hidden(esk5_0,X28) )
      & ( r1_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | r2_hidden(esk8_1(X28),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( r1_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_tarski(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) )
      & ( ~ r2_hidden(esk9_1(X28),X28)
        | ~ r2_hidden(k1_zfmisc_1(esk8_1(X28)),X28)
        | ~ r2_hidden(esk7_1(X28),X28)
        | ~ r2_hidden(esk5_0,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X19,X21,X22,X23,X25,X26] :
      ( r2_hidden(X19,esk3_1(X19))
      & ( ~ r2_hidden(X21,esk3_1(X19))
        | ~ r1_tarski(X22,X21)
        | r2_hidden(X22,esk3_1(X19)) )
      & ( r2_hidden(esk4_2(X19,X23),esk3_1(X19))
        | ~ r2_hidden(X23,esk3_1(X19)) )
      & ( ~ r1_tarski(X25,X23)
        | r2_hidden(X25,esk4_2(X19,X23))
        | ~ r2_hidden(X23,esk3_1(X19)) )
      & ( ~ r1_tarski(X26,esk3_1(X19))
        | r2_tarski(X26,esk3_1(X19))
        | r2_hidden(X26,esk3_1(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | r2_hidden(esk8_1(X1),X1)
    | r2_hidden(esk6_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_tarski(X1,esk3_1(X2))
    | r2_hidden(X1,esk3_1(X2))
    | ~ r1_tarski(X1,esk3_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | r2_hidden(esk6_1(X1),X1)
    | ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,esk3_1(X2))
    | ~ r2_hidden(X1,esk3_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | r2_hidden(esk8_1(X1),X1)
    | r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(X1,esk3_1(esk5_0))
    | ~ r1_tarski(X1,esk6_1(esk3_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk7_1(esk3_1(esk5_0)),esk6_1(esk3_1(esk5_0)))
    | r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | r2_hidden(esk8_1(X1),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8])]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | r2_hidden(esk6_1(X1),X1)
    | ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_30,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X6)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r1_tarski(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | ~ r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_2(X1,X2),esk3_1(X1))
    | ~ r2_hidden(X2,esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_32,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(X1,esk3_1(esk5_0))
    | ~ r1_tarski(X1,esk6_1(esk3_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk7_1(esk3_1(esk5_0)),esk6_1(esk3_1(esk5_0)))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_8])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,esk3_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X3))
    | ~ r2_hidden(X3,esk3_1(X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X1)
    | ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_2(X1,esk4_2(X2,X3)),X1)
    | r2_hidden(X1,esk3_1(X2))
    | ~ r2_hidden(X3,esk3_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_8])]),c_0_27])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))),X1)
    | r2_hidden(X1,esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))),k1_zfmisc_1(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))))
    | r2_hidden(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))),esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))))
    | r2_hidden(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_43])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk4_2(X3,X2))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,esk3_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,esk3_1(esk5_0))
    | ~ r1_tarski(X1,esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk4_2(esk5_0,esk8_1(esk3_1(esk5_0))))
    | ~ r1_tarski(X1,esk8_1(esk3_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))),X1)
    | r2_hidden(k1_zfmisc_1(X1),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk3_1(esk5_0))
    | ~ r2_hidden(esk2_2(X1,esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))),esk4_2(esk5_0,esk8_1(esk3_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_1(X1),X1)
    | ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(esk8_1(esk3_1(esk5_0))),esk3_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | ~ r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_8])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | r2_hidden(esk6_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk3_1(esk5_0))
    | ~ r1_tarski(X1,esk6_1(esk3_1(esk5_0)))
    | ~ r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk7_1(esk3_1(esk5_0)),esk6_1(esk3_1(esk5_0)))
    | ~ r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_8])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | ~ r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_57]),c_0_8])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_8])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk6_1(X1),X1)
    | ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_69,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | ~ r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_57]),c_0_8])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk6_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_57]),c_0_8])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk9_1(X1),X1)
    | r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_74,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0))
    | ~ r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_70]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,esk3_1(esk5_0))
    | ~ r1_tarski(X1,esk6_1(esk3_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk7_1(esk3_1(esk5_0)),esk6_1(esk3_1(esk5_0)))
    | r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_57]),c_0_8])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk7_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_57]),c_0_8])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk7_1(X1),esk6_1(X1))
    | ~ r2_tarski(esk9_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk8_1(X1)),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_80,negated_conjecture,
    ( r2_tarski(esk9_1(esk3_1(esk5_0)),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_78]),c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk7_1(esk3_1(esk5_0)),esk6_1(esk3_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_57]),c_0_8])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_81]),c_0_77]),
    [proof]).

%------------------------------------------------------------------------------
