%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:56 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 627 expanded)
%              Number of clauses        :   44 ( 239 expanded)
%              Number of leaves         :    6 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 (3415 expanded)
%              Number of equality atoms :   47 ( 604 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(t22_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ( X9 != k1_funct_1(X7,X8)
        | r2_hidden(k4_tarski(X8,X9),X7)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X8,X9),X7)
        | X9 = k1_funct_1(X7,X8)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_funct_1(X7,X8)
        | X9 = k1_xboole_0
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_xboole_0
        | X9 = k1_funct_1(X7,X8)
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
             => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & r2_hidden(esk8_0,k1_relat_1(k5_relat_1(esk10_0,esk9_0)))
    & k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0) != k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(k4_tarski(X12,esk1_3(X10,X11,X12)),X10)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X10)
        | r2_hidden(X14,X11)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | ~ r2_hidden(k4_tarski(esk2_2(X16,X17),X19),X16)
        | X17 = k1_relat_1(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r2_hidden(k4_tarski(esk2_2(X16,X17),esk3_2(X16,X17)),X16)
        | X17 = k1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24,X25,X27,X28,X29,X32] :
      ( ( r2_hidden(k4_tarski(X24,esk4_5(X21,X22,X23,X24,X25)),X21)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk4_5(X21,X22,X23,X24,X25),X25),X22)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X27,X29),X21)
        | ~ r2_hidden(k4_tarski(X29,X28),X22)
        | r2_hidden(k4_tarski(X27,X28),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X21,X22,X23),esk6_3(X21,X22,X23)),X23)
        | ~ r2_hidden(k4_tarski(esk5_3(X21,X22,X23),X32),X21)
        | ~ r2_hidden(k4_tarski(X32,esk6_3(X21,X22,X23)),X22)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk5_3(X21,X22,X23),esk7_3(X21,X22,X23)),X21)
        | r2_hidden(k4_tarski(esk5_3(X21,X22,X23),esk6_3(X21,X22,X23)),X23)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk7_3(X21,X22,X23),esk6_3(X21,X22,X23)),X22)
        | r2_hidden(k4_tarski(esk5_3(X21,X22,X23),esk6_3(X21,X22,X23)),X23)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | v1_relat_1(k5_relat_1(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(k5_relat_1(esk10_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ( v1_relat_1(k5_relat_1(X36,X37))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_1(k5_relat_1(X36,X37))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0)),k5_relat_1(esk10_0,esk9_0))
    | ~ v1_funct_1(k5_relat_1(esk10_0,esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0)),k5_relat_1(esk10_0,esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0)),k5_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_23]),c_0_24])])).

cnf(c_0_35,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_18])).

cnf(c_0_37,plain,
    ( esk1_3(X1,k1_relat_1(X1),X2) = k1_funct_1(X1,X2)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23]),c_0_24])])).

cnf(c_0_39,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(esk1_3(X3,k1_relat_1(X3),X1),X2),X4)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk1_3(esk10_0,k1_relat_1(esk10_0),esk8_0) = k1_funct_1(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_22]),c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_23])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,X1),k5_relat_1(esk10_0,X2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk10_0,esk8_0),X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_41]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk9_0,X1)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_42]),c_0_21]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) = k1_xboole_0
    | r2_hidden(k4_tarski(esk8_0,k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0))),k5_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0) != k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) = k1_xboole_0
    | ~ v1_funct_1(k5_relat_1(esk10_0,esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,plain,
    ( esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4) = k1_funct_1(X1,X3)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( esk4_5(esk10_0,esk9_0,k5_relat_1(esk10_0,esk9_0),esk8_0,k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0)) = k1_funct_1(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_34]),c_0_22]),c_0_24]),c_0_23])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk10_0,esk8_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_23]),c_0_24])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk10_0,esk8_0),k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_34]),c_0_23]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk8_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_54]),c_0_53]),c_0_21]),c_0_23])]),c_0_55]),
    [proof]).

%------------------------------------------------------------------------------
