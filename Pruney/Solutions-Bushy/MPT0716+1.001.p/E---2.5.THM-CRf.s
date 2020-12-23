%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0716+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:05 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  135 (17527836 expanded)
%              Number of clauses        :  126 (7392957 expanded)
%              Number of leaves         :    4 (4128950 expanded)
%              Depth                    :   87
%              Number of atoms          :  467 (111068274 expanded)
%              Number of equality atoms :   56 (9188343 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & ( ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
      | ~ r1_tarski(esk7_0,k1_relat_1(esk5_0))
      | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) )
    & ( r1_tarski(esk7_0,k1_relat_1(esk5_0))
      | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) )
    & ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
      | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r1_tarski(esk7_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X9 = k1_funct_1(X6,esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X12,k1_relat_1(X6))
        | ~ r2_hidden(X12,X7)
        | X11 != k1_funct_1(X6,X12)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X6))
        | ~ r2_hidden(X16,X13)
        | esk2_3(X6,X13,X14) != k1_funct_1(X6,X16)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk2_3(X6,X13,X14) = k1_funct_1(X6,esk3_3(X6,X13,X14))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k1_funct_1(X1,esk1_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),X1)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(X1,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(X1,X2))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(X1)),esk7_0)
    | ~ r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,k1_relat_1(X26))
        | ~ r2_hidden(X24,k1_relat_1(k5_relat_1(X26,X25)))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(k1_funct_1(X26,X24),k1_relat_1(X25))
        | ~ r2_hidden(X24,k1_relat_1(k5_relat_1(X26,X25)))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X24,k1_relat_1(X26))
        | ~ r2_hidden(k1_funct_1(X26,X24),k1_relat_1(X25))
        | r2_hidden(X24,k1_relat_1(k5_relat_1(X26,X25)))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(X1,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(X1,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(X1)),esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(X1)),esk7_0)
    | ~ r2_hidden(k1_funct_1(X1,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(esk5_0))
    | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(esk5_0))
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_41]),c_0_16]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,k1_relat_1(esk5_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_44])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_8])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_8])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_52]),c_0_16]),c_0_17])])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_55]),c_0_16]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,X1)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_55]),c_0_16]),c_0_17])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_34]),c_0_35])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_65])).

cnf(c_0_68,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_66]),c_0_12])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_8])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)))) = esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_70]),c_0_16]),c_0_17])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_73]),c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(esk5_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_75]),c_0_34]),c_0_16]),c_0_35]),c_0_17])]),c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,X1))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_76]),c_0_16]),c_0_17])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,X1)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_76]),c_0_16]),c_0_17])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),X1)
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),X1),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,X1)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(X1)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_34]),c_0_35])]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_8])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),esk7_0)
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_86]),c_0_16]),c_0_17])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_89]),c_0_72]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0)
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_95]),c_0_34]),c_0_35])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_97]),c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(esk5_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(esk5_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_101]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_103])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_8])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_8])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),esk7_0)
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_106]),c_0_16]),c_0_17])])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_107]),c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_108]),c_0_72]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_109]),c_0_36])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_111]),c_0_34]),c_0_16]),c_0_35]),c_0_17])]),c_0_112])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_113]),c_0_16]),c_0_17])])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,X1)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_113]),c_0_16]),c_0_17])])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(esk6_0))
    | r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_34]),c_0_35])])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k9_relat_1(esk5_0,esk7_0))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_8])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),esk7_0)
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_122]),c_0_16]),c_0_17])])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk7_0,k9_relat_1(esk5_0,esk7_0),esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0)))
    | r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_125]),c_0_72]),c_0_34]),c_0_16]),c_0_35]),c_0_17])])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk7_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_126])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_127])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k9_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0)))),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))),k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_131]),c_0_34]),c_0_35])])).

cnf(c_0_133,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_relat_1(k5_relat_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_127])])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_132]),c_0_133]),
    [proof]).

%------------------------------------------------------------------------------
