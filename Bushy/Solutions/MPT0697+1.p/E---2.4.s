%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t152_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 264.94s
% Output     : CNFRefutation 264.94s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 150 expanded)
%              Number of clauses        :   28 (  58 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  215 ( 770 expanded)
%              Number of equality atoms :   42 (  93 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t152_funct_1.p',t152_funct_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t152_funct_1.p',d13_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t152_funct_1.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t152_funct_1.p',d12_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t152_funct_1.p',d8_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

fof(c_0_6,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28] :
      ( ( r2_hidden(X25,k1_relat_1(X22))
        | ~ r2_hidden(X25,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(k1_funct_1(X22,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X26,k1_relat_1(X22))
        | ~ r2_hidden(k1_funct_1(X22,X26),X23)
        | r2_hidden(X26,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk6_3(X22,X27,X28),X28)
        | ~ r2_hidden(esk6_3(X22,X27,X28),k1_relat_1(X22))
        | ~ r2_hidden(k1_funct_1(X22,esk6_3(X22,X27,X28)),X27)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk6_3(X22,X27,X28),k1_relat_1(X22))
        | r2_hidden(esk6_3(X22,X27,X28),X28)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(k1_funct_1(X22,esk6_3(X22,X27,X28)),X27)
        | r2_hidden(esk6_3(X22,X27,X28),X28)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( ~ r1_tarski(X30,X31)
        | ~ r2_hidden(X32,X30)
        | r2_hidden(X32,X31) )
      & ( r2_hidden(esk7_2(X33,X34),X33)
        | r1_tarski(X33,X34) )
      & ( ~ r2_hidden(esk7_2(X33,X34),X34)
        | r1_tarski(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(esk3_4(X10,X11,X12,X13),k1_relat_1(X10))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk3_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X13 = k1_funct_1(X10,esk3_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X16,k1_relat_1(X10))
        | ~ r2_hidden(X16,X11)
        | X15 != k1_funct_1(X10,X16)
        | r2_hidden(X15,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk4_3(X10,X17,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X10))
        | ~ r2_hidden(X20,X17)
        | esk4_3(X10,X17,X18) != k1_funct_1(X10,X20)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),k1_relat_1(X10))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),X17)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk4_3(X10,X17,X18) = k1_funct_1(X10,esk5_3(X10,X17,X18))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v2_funct_1(X36)
        | ~ r2_hidden(X37,k1_relat_1(X36))
        | ~ r2_hidden(X38,k1_relat_1(X36))
        | k1_funct_1(X36,X37) != k1_funct_1(X36,X38)
        | X37 = X38
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk8_1(X36),k1_relat_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk9_1(X36),k1_relat_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( k1_funct_1(X36,esk8_1(X36)) = k1_funct_1(X36,esk9_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( esk8_1(X36) != esk9_1(X36)
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)),k9_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(X2,esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( X1 = esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_17]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_17]),c_0_18])])).

cnf(c_0_30,plain,
    ( k1_funct_1(X1,esk3_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))) = esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)
    | k1_funct_1(esk2_0,esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)))) != k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)))) = k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_17]),c_0_18])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_17]),c_0_18])])).

cnf(c_0_36,negated_conjecture,
    ( esk3_4(esk2_0,esk1_0,k9_relat_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))) = esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk7_2(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
