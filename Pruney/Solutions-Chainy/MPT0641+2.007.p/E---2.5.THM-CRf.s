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
% DateTime   : Thu Dec  3 10:53:40 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 911 expanded)
%              Number of clauses        :   55 ( 324 expanded)
%              Number of leaves         :   10 ( 217 expanded)
%              Depth                    :   17
%              Number of atoms          :  289 (5314 expanded)
%              Number of equality atoms :   59 ( 769 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(k5_relat_1(X2,X1))
                & k2_relat_1(X2) = k1_relat_1(X1) )
             => ( v2_funct_1(X2)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_funct_1])).

fof(c_0_11,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v2_funct_1(k5_relat_1(X33,X32))
      | ~ r1_tarski(k2_relat_1(X33),k1_relat_1(X32))
      | v2_funct_1(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(k5_relat_1(esk7_0,esk6_0))
    & k2_relat_1(esk7_0) = k1_relat_1(esk6_0)
    & ( ~ v2_funct_1(esk7_0)
      | ~ v2_funct_1(esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk7_0)
    | ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r1_tarski(k2_relat_1(X20),k1_relat_1(X21))
      | k1_relat_1(k5_relat_1(X20,X21)) = k1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_funct_1(X22)
        | ~ r2_hidden(X23,k1_relat_1(X22))
        | ~ r2_hidden(X24,k1_relat_1(X22))
        | k1_funct_1(X22,X23) != k1_funct_1(X22,X24)
        | X23 = X24
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk4_1(X22),k1_relat_1(X22))
        | v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk5_1(X22),k1_relat_1(X22))
        | v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_funct_1(X22,esk4_1(X22)) = k1_funct_1(X22,esk5_1(X22))
        | v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk4_1(X22) != esk5_1(X22)
        | v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_funct_1(esk7_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_31,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,k1_relat_1(X36))
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( X35 = k1_funct_1(X36,X34)
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X34,k1_relat_1(X36))
        | X35 != k1_funct_1(X36,X34)
        | r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),X1),X1),esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(esk5_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk7_0,X1)) = k1_relat_1(esk7_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_19])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),esk5_1(esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_20])]),c_0_36])).

cnf(c_0_41,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk7_0,esk6_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_20])])).

fof(c_0_43,plain,(
    ! [X27,X28] :
      ( ( v1_relat_1(k5_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k5_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_16])])).

cnf(c_0_47,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | v1_relat_1(k5_relat_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_49,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
      | k1_funct_1(k5_relat_1(X31,X30),X29) = k1_funct_1(X30,k1_funct_1(X31,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(esk6_0),k1_funct_1(esk6_0,esk5_1(esk6_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_18]),c_0_20])])).

cnf(c_0_51,plain,
    ( k1_funct_1(X1,esk4_1(X1)) = k1_funct_1(X1,esk5_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_18]),c_0_17]),c_0_20]),c_0_19])])).

cnf(c_0_53,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(esk6_0),k1_funct_1(esk6_0,esk4_1(esk6_0))),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_18]),c_0_20])]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_19])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_40]),c_0_17]),c_0_19])])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) = k1_funct_1(esk6_0,k1_funct_1(esk7_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))) = esk5_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_17]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_1(esk6_0)) = k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_18]),c_0_20])])).

cnf(c_0_63,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( X1 = esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))) = k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),esk4_1(esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_18]),c_0_20])]),c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( X1 = esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(esk6_0,esk4_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_17]),c_0_19])])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) = esk4_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_66]),c_0_17]),c_0_19])])).

cnf(c_0_70,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) != k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) = k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_68]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_73,plain,
    ( v2_funct_1(X1)
    | esk4_1(X1) != esk5_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( esk5_1(esk6_0) = esk4_1(esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_72]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_18]),c_0_20])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.37  # and selection function SelectNewComplexAHPNS.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t48_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 0.13/0.37  fof(t47_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))=>v2_funct_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.37  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 0.13/0.37  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.13/0.37  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.37  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.13/0.37  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.37  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1)))))), inference(assume_negation,[status(cth)],[t48_funct_1])).
% 0.13/0.37  fof(c_0_11, plain, ![X32, X33]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v2_funct_1(k5_relat_1(X33,X32))|~r1_tarski(k2_relat_1(X33),k1_relat_1(X32))|v2_funct_1(X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v2_funct_1(k5_relat_1(esk7_0,esk6_0))&k2_relat_1(esk7_0)=k1_relat_1(esk6_0))&(~v2_funct_1(esk7_0)|~v2_funct_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:(((~r2_hidden(X9,X8)|r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)|X8!=k2_relat_1(X7))&(~r2_hidden(k4_tarski(X12,X11),X7)|r2_hidden(X11,X8)|X8!=k2_relat_1(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.37  cnf(c_0_15, plain, (v2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X1))|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v2_funct_1(k5_relat_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (k2_relat_1(esk7_0)=k1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (v2_funct_1(esk7_0)|~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.37  fof(c_0_26, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r1_tarski(k2_relat_1(X20),k1_relat_1(X21))|k1_relat_1(k5_relat_1(X20,X21))=k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.13/0.37  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_28, plain, ![X22, X23, X24]:((~v2_funct_1(X22)|(~r2_hidden(X23,k1_relat_1(X22))|~r2_hidden(X24,k1_relat_1(X22))|k1_funct_1(X22,X23)!=k1_funct_1(X22,X24)|X23=X24)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&((((r2_hidden(esk4_1(X22),k1_relat_1(X22))|v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(esk5_1(X22),k1_relat_1(X22))|v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(k1_funct_1(X22,esk4_1(X22))=k1_funct_1(X22,esk5_1(X22))|v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(esk4_1(X22)!=esk5_1(X22)|v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~v2_funct_1(esk7_0)|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.13/0.37  cnf(c_0_31, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  fof(c_0_32, plain, ![X34, X35, X36]:(((r2_hidden(X34,k1_relat_1(X36))|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(X35=k1_funct_1(X36,X34)|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(~r2_hidden(X34,k1_relat_1(X36))|X35!=k1_funct_1(X36,X34)|r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),X1),X1),esk7_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.13/0.37  cnf(c_0_35, plain, (r2_hidden(esk5_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k1_relat_1(k5_relat_1(esk7_0,X1))=k1_relat_1(esk7_0)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_19])])).
% 0.13/0.37  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_39, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),esk5_1(esk6_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_20])]), c_0_36])).
% 0.13/0.37  cnf(c_0_41, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k1_relat_1(k5_relat_1(esk7_0,esk6_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_20])])).
% 0.13/0.37  fof(c_0_43, plain, ![X27, X28]:((v1_relat_1(k5_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)|~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k5_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)|~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.13/0.37  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_1(esk6_0),k1_relat_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_16])])).
% 0.13/0.37  cnf(c_0_47, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.37  fof(c_0_48, plain, ![X18, X19]:(~v1_relat_1(X18)|~v1_relat_1(X19)|v1_relat_1(k5_relat_1(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.37  fof(c_0_49, plain, ![X29, X30, X31]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))|k1_funct_1(k5_relat_1(X31,X30),X29)=k1_funct_1(X30,k1_funct_1(X31,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(esk6_0),k1_funct_1(esk6_0,esk5_1(esk6_0))),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_18]), c_0_20])])).
% 0.13/0.37  cnf(c_0_51, plain, (k1_funct_1(X1,esk4_1(X1))=k1_funct_1(X1,esk5_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_18]), c_0_17]), c_0_20]), c_0_19])])).
% 0.13/0.37  cnf(c_0_53, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.37  cnf(c_0_54, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_55, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.37  cnf(c_0_56, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(esk6_0),k1_funct_1(esk6_0,esk4_1(esk6_0))),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_18]), c_0_20])]), c_0_36])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_20]), c_0_19])])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_40]), c_0_17]), c_0_19])])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)=k1_funct_1(esk6_0,k1_funct_1(esk7_0,X1))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))=esk5_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_17]), c_0_19])])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk6_0,esk5_1(esk6_0))=k1_funct_1(esk6_0,esk4_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_18]), c_0_20])])).
% 0.13/0.37  cnf(c_0_63, plain, (r2_hidden(esk4_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, (X1=esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.37  cnf(c_0_65, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))=k1_funct_1(esk6_0,esk4_1(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_61]), c_0_62])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),esk4_1(esk6_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_63]), c_0_18]), c_0_20])]), c_0_36])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, (X1=esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(esk6_0,esk4_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.37  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_66]), c_0_17]), c_0_19])])).
% 0.13/0.37  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))=esk4_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_66]), c_0_17]), c_0_19])])).
% 0.13/0.37  cnf(c_0_70, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))!=k1_funct_1(esk6_0,esk4_1(esk6_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.37  cnf(c_0_71, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))=k1_funct_1(esk6_0,esk4_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_68]), c_0_69])).
% 0.13/0.37  cnf(c_0_72, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.13/0.37  cnf(c_0_73, plain, (v2_funct_1(X1)|esk4_1(X1)!=esk5_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_74, negated_conjecture, (esk5_1(esk6_0)=esk4_1(esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_72]), c_0_69])).
% 0.13/0.37  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_18]), c_0_20])]), c_0_36]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 76
% 0.13/0.37  # Proof object clause steps            : 55
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 38
% 0.13/0.37  # Proof object clause conjectures      : 35
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 23
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 23
% 0.13/0.37  # Proof object simplifying inferences  : 76
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 28
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 28
% 0.13/0.37  # Processed clauses                    : 82
% 0.13/0.37  # ...of these trivial                  : 3
% 0.13/0.37  # ...subsumed                          : 4
% 0.13/0.37  # ...remaining for further processing  : 75
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 6
% 0.13/0.37  # Backward-rewritten                   : 17
% 0.13/0.37  # Generated clauses                    : 106
% 0.13/0.37  # ...of the previous two non-trivial   : 86
% 0.13/0.37  # Contextual simplify-reflections      : 4
% 0.13/0.37  # Paramodulations                      : 101
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 5
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 47
% 0.13/0.37  #    Positive orientable unit clauses  : 17
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 29
% 0.13/0.37  # Current number of unprocessed clauses: 32
% 0.13/0.37  # ...number of literals in the above   : 105
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 23
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 242
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 45
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.37  # Unit Clause-clause subsumption calls : 85
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 18
% 0.13/0.37  # BW rewrite match successes           : 7
% 0.13/0.37  # Condensation attempts                : 82
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 5700
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
