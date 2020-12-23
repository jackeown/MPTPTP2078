%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t136_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 159.52s
% Output     : CNFRefutation 159.52s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 308 expanded)
%              Number of clauses        :   59 ( 134 expanded)
%              Number of leaves         :    4 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  313 (3463 expanded)
%              Number of equality atoms :   22 (  88 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   72 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t136_zfmisc_1.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t136_zfmisc_1.p',t136_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t136_zfmisc_1.p',d1_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t136_zfmisc_1.p',t9_tarski)).

fof(c_0_4,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk7_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk7_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | r1_tarski(X16,X14)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r1_tarski(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r2_hidden(esk6_2(X18,X19),X19)
        | ~ r1_tarski(esk6_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) )
      & ( r2_hidden(esk6_2(X18,X19),X19)
        | r1_tarski(esk6_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_9,negated_conjecture,(
    ! [X7] :
      ( ( r1_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( r1_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r2_hidden(esk2_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( r1_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( r1_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | r1_tarski(esk3_1(X7),esk2_1(X7))
        | ~ r2_hidden(esk1_0,X7) )
      & ( r1_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | r2_hidden(esk4_1(X7),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( r1_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_tarski(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) )
      & ( ~ r2_hidden(esk5_1(X7),X7)
        | ~ r2_hidden(k1_zfmisc_1(esk4_1(X7)),X7)
        | ~ r2_hidden(esk3_1(X7),X7)
        | ~ r2_hidden(esk1_0,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_10,plain,(
    ! [X32,X34,X35,X36,X38,X39] :
      ( r2_hidden(X32,esk8_1(X32))
      & ( ~ r2_hidden(X34,esk8_1(X32))
        | ~ r1_tarski(X35,X34)
        | r2_hidden(X35,esk8_1(X32)) )
      & ( r2_hidden(esk9_2(X32,X36),esk8_1(X32))
        | ~ r2_hidden(X36,esk8_1(X32)) )
      & ( ~ r1_tarski(X38,X36)
        | r2_hidden(X38,esk9_2(X32,X36))
        | ~ r2_hidden(X36,esk8_1(X32)) )
      & ( ~ r1_tarski(X39,esk8_1(X32))
        | r2_tarski(X39,esk8_1(X32))
        | r2_hidden(X39,esk8_1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_tarski(X1,esk8_1(X2))
    | r2_hidden(X1,esk8_1(X2))
    | ~ r1_tarski(X1,esk8_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | r2_hidden(esk4_1(X1),X1)
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,esk8_1(X2))
    | ~ r2_hidden(X1,esk8_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(X1)),esk8_1(X1))
    | r2_hidden(esk4_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2)
    | X3 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,esk9_2(X3,X2))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,esk8_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( r1_tarski(esk7_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | X1 != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(X1)),esk8_1(X1))
    | r2_hidden(X2,esk8_1(X1))
    | ~ r1_tarski(X2,esk4_1(esk8_1(X1)))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk9_2(X1,X2),esk8_1(X1))
    | ~ r2_hidden(X2,esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_2(X1,X2),esk9_2(X3,X4))
    | X1 != k1_zfmisc_1(X4)
    | ~ r2_hidden(X4,esk8_1(X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(X1)),esk8_1(X1))
    | r2_hidden(X2,esk8_1(X1))
    | k1_zfmisc_1(esk4_1(esk8_1(X1))) != k1_zfmisc_1(X2)
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,esk8_1(X2))
    | ~ r1_tarski(X1,esk9_2(X2,X3))
    | ~ r2_hidden(X3,esk8_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,esk9_2(X2,X3))
    | X1 != k1_zfmisc_1(X3)
    | ~ r2_hidden(X3,esk8_1(X2)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | r2_hidden(X1,esk8_1(esk1_0))
    | k1_zfmisc_1(esk4_1(esk8_1(esk1_0))) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,esk8_1(X2))
    | X1 != k1_zfmisc_1(X3)
    | ~ r2_hidden(X3,esk8_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | r2_hidden(esk2_1(esk8_1(esk1_0)),esk8_1(esk1_0)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | r2_hidden(X1,esk8_1(esk1_0))
    | X1 != k1_zfmisc_1(esk4_1(esk8_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(X1))),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(esk1_0))),esk8_1(esk1_0))
    | r2_hidden(esk2_1(esk8_1(esk1_0)),esk8_1(esk1_0)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_1(esk1_0)),esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | r2_hidden(esk4_1(X1),X1)
    | r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | r2_hidden(esk4_1(X1),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_1(X1),X1)
    | ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk8_1(esk1_0))
    | ~ r1_tarski(X1,esk2_1(esk8_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk3_1(esk8_1(X1)),esk2_1(esk8_1(X1)))
    | r2_hidden(esk4_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_43]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk3_1(X1),esk2_1(X1))
    | ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(esk3_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_14]),c_0_46]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | r2_hidden(esk3_1(esk8_1(esk1_0)),esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(X1)),X1)
    | ~ r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_1(esk8_1(X1)),esk2_1(esk8_1(X1)))
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(X1))),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_51]),c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_1(esk1_0)),esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(X1))),esk8_1(X1))
    | ~ r2_hidden(esk3_1(esk8_1(X1)),esk8_1(X1))
    | ~ r2_hidden(esk1_0,esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_14]),c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | ~ r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(esk1_0))),esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_29])])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,esk8_1(esk1_0))
    | X1 != k1_zfmisc_1(esk4_1(esk8_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k1_zfmisc_1(esk4_1(esk8_1(esk1_0))),esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(esk8_1(esk1_0))
    | X1 != k1_zfmisc_1(esk4_1(esk8_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
