%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0689+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:02 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (1335 expanded)
%              Number of clauses        :   61 ( 535 expanded)
%              Number of leaves         :    5 ( 308 expanded)
%              Depth                    :   19
%              Number of atoms          :  331 (8307 expanded)
%              Number of equality atoms :   97 (2033 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t144_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ~ ( r2_hidden(X2,k2_relat_1(X1))
              & ! [X3] : k10_relat_1(X1,k1_tarski(X2)) != k1_tarski(X3) )
      <=> v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2] :
              ~ ( r2_hidden(X2,k2_relat_1(X1))
                & ! [X3] : k10_relat_1(X1,k1_tarski(X2)) != k1_tarski(X3) )
        <=> v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t144_funct_1])).

fof(c_0_6,plain,(
    ! [X20,X21,X22,X24,X25,X26,X28] :
      ( ( r2_hidden(esk3_3(X20,X21,X22),k1_relat_1(X20))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 = k1_funct_1(X20,esk3_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X25,k1_relat_1(X20))
        | X24 != k1_funct_1(X20,X25)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(esk4_2(X20,X26),X26)
        | ~ r2_hidden(X28,k1_relat_1(X20))
        | esk4_2(X20,X26) != k1_funct_1(X20,X28)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk5_2(X20,X26),k1_relat_1(X20))
        | r2_hidden(esk4_2(X20,X26),X26)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( esk4_2(X20,X26) = k1_funct_1(X20,esk5_2(X20,X26))
        | r2_hidden(esk4_2(X20,X26),X26)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_7,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_funct_1(X30)
        | ~ r2_hidden(X31,k1_relat_1(X30))
        | ~ r2_hidden(X32,k1_relat_1(X30))
        | k1_funct_1(X30,X31) != k1_funct_1(X30,X32)
        | X31 = X32
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( r2_hidden(esk6_1(X30),k1_relat_1(X30))
        | v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( r2_hidden(esk7_1(X30),k1_relat_1(X30))
        | v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( k1_funct_1(X30,esk6_1(X30)) = k1_funct_1(X30,esk7_1(X30))
        | v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( esk6_1(X30) != esk7_1(X30)
        | v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X37,X38] :
      ( v1_relat_1(esk8_0)
      & v1_funct_1(esk8_0)
      & ( r2_hidden(esk9_0,k2_relat_1(esk8_0))
        | ~ v2_funct_1(esk8_0) )
      & ( k10_relat_1(esk8_0,k1_tarski(esk9_0)) != k1_tarski(X37)
        | ~ v2_funct_1(esk8_0) )
      & ( ~ r2_hidden(X38,k2_relat_1(esk8_0))
        | k10_relat_1(esk8_0,k1_tarski(X38)) = k1_tarski(esk10_1(X38))
        | v2_funct_1(esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( r2_hidden(X8,k1_relat_1(X5))
        | ~ r2_hidden(X8,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(k1_funct_1(X5,X8),X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(X9,k1_relat_1(X5))
        | ~ r2_hidden(k1_funct_1(X5,X9),X6)
        | r2_hidden(X9,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | ~ r2_hidden(esk1_3(X5,X10,X11),k1_relat_1(X5))
        | ~ r2_hidden(k1_funct_1(X5,esk1_3(X5,X10,X11)),X10)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(esk1_3(X5,X10,X11),k1_relat_1(X5))
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(k1_funct_1(X5,esk1_3(X5,X10,X11)),X10)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k1_funct_1(X1,esk6_1(X1)) = k1_funct_1(X1,esk7_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk7_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(X1)) = k1_tarski(esk10_1(X1))
    | v2_funct_1(esk8_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_11])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_1(esk8_0)) = k1_funct_1(esk8_0,esk6_1(esk8_0))
    | v2_funct_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( v2_funct_1(esk8_0)
    | r2_hidden(esk7_1(esk8_0),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_14])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(k1_funct_1(esk8_0,X1))) = k1_tarski(esk10_1(k1_funct_1(esk8_0,X1)))
    | v2_funct_1(esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13]),c_0_14])])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk8_0)
    | r2_hidden(k1_funct_1(esk8_0,esk6_1(esk8_0)),k2_relat_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_14])]),c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk6_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k1_tarski(k1_funct_1(X2,X1))))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(k1_funct_1(esk8_0,esk7_1(esk8_0)))) = k1_tarski(esk10_1(k1_funct_1(esk8_0,esk7_1(esk8_0))))
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(k1_funct_1(esk8_0,esk6_1(esk8_0)))) = k1_tarski(esk10_1(k1_funct_1(esk8_0,esk6_1(esk8_0))))
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk8_0)
    | r2_hidden(esk6_1(esk8_0),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_14])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk8_0)
    | r2_hidden(esk7_1(esk8_0),k1_tarski(esk10_1(k1_funct_1(esk8_0,esk7_1(esk8_0))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13]),c_0_14])]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk8_0)
    | r2_hidden(esk6_1(esk8_0),k1_tarski(esk10_1(k1_funct_1(esk8_0,esk6_1(esk8_0))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_13]),c_0_14])]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk10_1(k1_funct_1(esk8_0,esk7_1(esk8_0))) = esk7_1(esk8_0)
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( esk10_1(k1_funct_1(esk8_0,esk6_1(esk8_0))) = esk6_1(esk8_0)
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk10_1(k1_funct_1(esk8_0,esk6_1(esk8_0))) = esk7_1(esk8_0)
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v2_funct_1(X1)
    | esk6_1(X1) != esk7_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( esk7_1(esk8_0) = esk6_1(esk8_0)
    | v2_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k1_funct_1(X1,X2) = X3
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_tarski(X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk8_0))
    | ~ v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_13]),c_0_14])])).

cnf(c_0_50,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X3
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_tarski(X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)) = X1
    | ~ r2_hidden(esk9_0,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_13]),c_0_14])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,plain,
    ( X1 = esk3_3(X2,k2_relat_1(X2),X3)
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk3_3(X2,k2_relat_1(X2),X3))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X3,k2_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_59,plain,
    ( esk2_2(X1,k10_relat_1(X2,X3)) = X1
    | k10_relat_1(X2,X3) = k1_tarski(X1)
    | r2_hidden(esk2_2(X1,k10_relat_1(X2,X3)),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)
    | k1_funct_1(esk8_0,X1) != esk9_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_49]),c_0_51]),c_0_13]),c_0_14])])).

cnf(c_0_61,negated_conjecture,
    ( esk2_2(X1,k10_relat_1(esk8_0,X2)) = X1
    | k10_relat_1(esk8_0,X2) = k1_tarski(X1)
    | r2_hidden(esk2_2(X1,k10_relat_1(esk8_0,X2)),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_13]),c_0_14])])).

cnf(c_0_62,plain,
    ( k1_funct_1(X1,esk2_2(X2,k10_relat_1(X1,k1_tarski(X3)))) = X3
    | esk2_2(X2,k10_relat_1(X1,k1_tarski(X3))) = X2
    | k10_relat_1(X1,k1_tarski(X3)) = k1_tarski(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(esk9_0)) != k1_tarski(X1)
    | ~ v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_64,negated_conjecture,
    ( esk2_2(X1,k10_relat_1(esk8_0,X2)) = esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)
    | esk2_2(X1,k10_relat_1(esk8_0,X2)) = X1
    | k10_relat_1(esk8_0,X2) = k1_tarski(X1)
    | k1_funct_1(esk8_0,esk2_2(X1,k10_relat_1(esk8_0,X2))) != esk9_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk8_0,esk2_2(X1,k10_relat_1(esk8_0,k1_tarski(X2)))) = X2
    | esk2_2(X1,k10_relat_1(esk8_0,k1_tarski(X2))) = X1
    | k10_relat_1(esk8_0,k1_tarski(X2)) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_13]),c_0_14])])).

cnf(c_0_66,negated_conjecture,
    ( k10_relat_1(esk8_0,k1_tarski(esk9_0)) != k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_49])])).

cnf(c_0_67,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_68,negated_conjecture,
    ( esk2_2(X1,k10_relat_1(esk8_0,k1_tarski(esk9_0))) = esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)
    | esk2_2(X1,k10_relat_1(esk8_0,k1_tarski(esk9_0))) = X1 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65])]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( esk2_2(X1,k10_relat_1(esk8_0,k1_tarski(esk9_0))) = esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,k1_tarski(esk9_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk9_0),k10_relat_1(esk8_0,k1_tarski(esk9_0))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_69]),c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_47]),c_0_51]),c_0_23]),c_0_13]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
