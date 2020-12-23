%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 431 expanded)
%              Number of clauses        :   38 ( 160 expanded)
%              Number of leaves         :    9 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 (1776 expanded)
%              Number of equality atoms :  108 ( 947 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k1_relat_1(X3)
              & k2_relat_1(X2) = k1_tarski(X1)
              & k2_relat_1(X3) = k1_tarski(X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = k1_relat_1(X3)
                & k2_relat_1(X2) = k1_tarski(X1)
                & k2_relat_1(X3) = k1_tarski(X1) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk5_0) = k1_relat_1(esk6_0)
    & k2_relat_1(esk5_0) = k1_tarski(esk4_0)
    & k2_relat_1(esk6_0) = k1_tarski(esk4_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X17
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k2_enumset1(X17,X18,X19,X20) )
      & ( X23 != X17
        | r2_hidden(X23,X21)
        | X21 != k2_enumset1(X17,X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k2_enumset1(X17,X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k2_enumset1(X17,X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k2_enumset1(X17,X18,X19,X20) )
      & ( esk1_5(X24,X25,X26,X27,X28) != X24
        | ~ r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)
        | X28 = k2_enumset1(X24,X25,X26,X27) )
      & ( esk1_5(X24,X25,X26,X27,X28) != X25
        | ~ r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)
        | X28 = k2_enumset1(X24,X25,X26,X27) )
      & ( esk1_5(X24,X25,X26,X27,X28) != X26
        | ~ r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)
        | X28 = k2_enumset1(X24,X25,X26,X27) )
      & ( esk1_5(X24,X25,X26,X27,X28) != X27
        | ~ r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)
        | X28 = k2_enumset1(X24,X25,X26,X27) )
      & ( r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)
        | esk1_5(X24,X25,X26,X27,X28) = X24
        | esk1_5(X24,X25,X26,X27,X28) = X25
        | esk1_5(X24,X25,X26,X27,X28) = X26
        | esk1_5(X24,X25,X26,X27,X28) = X27
        | X28 = k2_enumset1(X24,X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(esk6_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X4,X5,X6)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(esk5_0) = k2_relat_1(esk6_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r2_hidden(X34,k1_relat_1(X35))
      | r2_hidden(k1_funct_1(X35,X34),k2_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

fof(c_0_28,plain,(
    ! [X36,X37] :
      ( ( r2_hidden(esk3_2(X36,X37),k1_relat_1(X36))
        | k1_relat_1(X36) != k1_relat_1(X37)
        | X36 = X37
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( k1_funct_1(X36,esk3_2(X36,X37)) != k1_funct_1(X37,esk3_2(X36,X37))
        | k1_relat_1(X36) != k1_relat_1(X37)
        | X36 = X37
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

fof(c_0_29,plain,(
    ! [X30,X31,X33] :
      ( v1_relat_1(esk2_2(X30,X31))
      & v1_funct_1(esk2_2(X30,X31))
      & k1_relat_1(esk2_2(X30,X31)) = X30
      & ( ~ r2_hidden(X33,X30)
        | k1_funct_1(esk2_2(X30,X31),X33) = X31 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k3_enumset1(X5,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk3_2(X1,X2)) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k1_funct_1(esk2_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v1_funct_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( v1_relat_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk3_2(X1,esk6_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_47,plain,
    ( esk2_2(k1_relat_1(X1),X2) = X1
    | k1_funct_1(X1,esk3_2(X1,esk2_2(k1_relat_1(X1),X2))) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,esk2_2(k1_relat_1(X1),X2)),k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43])])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk4_0
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( esk2_2(k1_relat_1(X1),X2) = X1
    | k1_funct_1(X1,esk3_2(esk2_2(k1_relat_1(X1),X2),X1)) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk3_2(esk2_2(k1_relat_1(X1),X2),X1),k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43])])])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_37]),c_0_38])])).

cnf(c_0_51,negated_conjecture,
    ( esk2_2(k1_relat_1(esk6_0),X1) = esk6_0
    | r2_hidden(esk3_2(esk2_2(k1_relat_1(esk6_0),X1),esk6_0),k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_41]),c_0_42]),c_0_43])])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( esk2_2(k1_relat_1(esk6_0),esk4_0) = esk5_0
    | ~ r2_hidden(esk3_2(esk5_0,esk2_2(k1_relat_1(esk6_0),esk4_0)),k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_33]),c_0_34]),c_0_35]),c_0_35]),c_0_35])])])).

cnf(c_0_54,negated_conjecture,
    ( esk2_2(k1_relat_1(esk6_0),esk4_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_37]),c_0_38])])]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_33]),c_0_34])]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54]),c_0_55])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t17_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.39  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 0.21/0.39  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.21/0.39  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.21/0.39  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.21/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3)))), inference(assume_negation,[status(cth)],[t17_funct_1])).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((k1_relat_1(esk5_0)=k1_relat_1(esk6_0)&k2_relat_1(esk5_0)=k1_tarski(esk4_0))&k2_relat_1(esk6_0)=k1_tarski(esk4_0))&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_12, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_13, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_14, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.39  fof(c_0_15, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X22,X21)|(X22=X17|X22=X18|X22=X19|X22=X20)|X21!=k2_enumset1(X17,X18,X19,X20))&((((X23!=X17|r2_hidden(X23,X21)|X21!=k2_enumset1(X17,X18,X19,X20))&(X23!=X18|r2_hidden(X23,X21)|X21!=k2_enumset1(X17,X18,X19,X20)))&(X23!=X19|r2_hidden(X23,X21)|X21!=k2_enumset1(X17,X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k2_enumset1(X17,X18,X19,X20))))&(((((esk1_5(X24,X25,X26,X27,X28)!=X24|~r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)|X28=k2_enumset1(X24,X25,X26,X27))&(esk1_5(X24,X25,X26,X27,X28)!=X25|~r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)|X28=k2_enumset1(X24,X25,X26,X27)))&(esk1_5(X24,X25,X26,X27,X28)!=X26|~r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)|X28=k2_enumset1(X24,X25,X26,X27)))&(esk1_5(X24,X25,X26,X27,X28)!=X27|~r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)|X28=k2_enumset1(X24,X25,X26,X27)))&(r2_hidden(esk1_5(X24,X25,X26,X27,X28),X28)|(esk1_5(X24,X25,X26,X27,X28)=X24|esk1_5(X24,X25,X26,X27,X28)=X25|esk1_5(X24,X25,X26,X27,X28)=X26|esk1_5(X24,X25,X26,X27,X28)=X27)|X28=k2_enumset1(X24,X25,X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.21/0.39  cnf(c_0_16, negated_conjecture, (k2_relat_1(esk6_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_20, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (k2_relat_1(esk5_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_22, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (k2_relat_1(esk6_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.21/0.39  cnf(c_0_25, plain, (X1=X6|X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X4,X5,X6)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (k2_relat_1(esk5_0)=k2_relat_1(esk6_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.39  fof(c_0_27, plain, ![X34, X35]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~r2_hidden(X34,k1_relat_1(X35))|r2_hidden(k1_funct_1(X35,X34),k2_relat_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.21/0.39  fof(c_0_28, plain, ![X36, X37]:((r2_hidden(esk3_2(X36,X37),k1_relat_1(X36))|k1_relat_1(X36)!=k1_relat_1(X37)|X36=X37|(~v1_relat_1(X37)|~v1_funct_1(X37))|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(k1_funct_1(X36,esk3_2(X36,X37))!=k1_funct_1(X37,esk3_2(X36,X37))|k1_relat_1(X36)!=k1_relat_1(X37)|X36=X37|(~v1_relat_1(X37)|~v1_funct_1(X37))|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.21/0.39  fof(c_0_29, plain, ![X30, X31, X33]:(((v1_relat_1(esk2_2(X30,X31))&v1_funct_1(esk2_2(X30,X31)))&k1_relat_1(esk2_2(X30,X31))=X30)&(~r2_hidden(X33,X30)|k1_funct_1(esk2_2(X30,X31),X33)=X31)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.21/0.39  cnf(c_0_30, plain, (X1=X2|X1=X3|X1=X4|X1=X5|~r2_hidden(X1,k3_enumset1(X5,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)), inference(rw,[status(thm)],[c_0_24, c_0_26])).
% 0.21/0.39  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk5_0)=k1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_36, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_39, plain, (X1=X2|k1_funct_1(X1,esk3_2(X1,X2))!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_40, plain, (k1_funct_1(esk2_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_41, plain, (k1_relat_1(esk2_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_42, plain, (v1_funct_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_43, plain, (v1_relat_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_33]), c_0_34]), c_0_35])])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (X1=esk6_0|r2_hidden(esk3_2(X1,esk6_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.21/0.39  cnf(c_0_47, plain, (esk2_2(k1_relat_1(X1),X2)=X1|k1_funct_1(X1,esk3_2(X1,esk2_2(k1_relat_1(X1),X2)))!=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk3_2(X1,esk2_2(k1_relat_1(X1),X2)),k1_relat_1(X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43])])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk4_0|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.39  cnf(c_0_49, plain, (esk2_2(k1_relat_1(X1),X2)=X1|k1_funct_1(X1,esk3_2(esk2_2(k1_relat_1(X1),X2),X1))!=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk3_2(esk2_2(k1_relat_1(X1),X2),X1),k1_relat_1(X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43])])])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_37]), c_0_38])])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (esk2_2(k1_relat_1(esk6_0),X1)=esk6_0|r2_hidden(esk3_2(esk2_2(k1_relat_1(esk6_0),X1),esk6_0),k1_relat_1(esk6_0))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_41]), c_0_42]), c_0_43])])])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (esk2_2(k1_relat_1(esk6_0),esk4_0)=esk5_0|~r2_hidden(esk3_2(esk5_0,esk2_2(k1_relat_1(esk6_0),esk4_0)),k1_relat_1(esk6_0))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_33]), c_0_34]), c_0_35]), c_0_35]), c_0_35])])])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (esk2_2(k1_relat_1(esk6_0),esk4_0)=esk6_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_37]), c_0_38])])]), c_0_51])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_33]), c_0_34])]), c_0_52])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54]), c_0_55])]), c_0_52]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 57
% 0.21/0.39  # Proof object clause steps            : 38
% 0.21/0.39  # Proof object formula steps           : 19
% 0.21/0.39  # Proof object conjectures             : 25
% 0.21/0.39  # Proof object clause conjectures      : 22
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 20
% 0.21/0.39  # Proof object initial formulas used   : 9
% 0.21/0.39  # Proof object generating inferences   : 11
% 0.21/0.39  # Proof object simplifying inferences  : 57
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 9
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 29
% 0.21/0.39  # Removed in clause preprocessing      : 4
% 0.21/0.39  # Initial clauses in saturation        : 25
% 0.21/0.39  # Processed clauses                    : 84
% 0.21/0.39  # ...of these trivial                  : 2
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 82
% 0.21/0.39  # Other redundant clauses eliminated   : 30
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 3
% 0.21/0.39  # Generated clauses                    : 212
% 0.21/0.39  # ...of the previous two non-trivial   : 165
% 0.21/0.39  # Contextual simplify-reflections      : 1
% 0.21/0.39  # Paramodulations                      : 183
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 33
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 49
% 0.21/0.39  #    Positive orientable unit clauses  : 27
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 21
% 0.21/0.39  # Current number of unprocessed clauses: 131
% 0.21/0.39  # ...number of literals in the above   : 832
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 32
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 118
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 75
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.39  # Unit Clause-clause subsumption calls : 40
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 59
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 7382
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.037 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.041 s
% 0.21/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
