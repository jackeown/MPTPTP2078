%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:56 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   92 (136254 expanded)
%              Number of clauses        :   73 (59768 expanded)
%              Number of leaves         :    9 (34493 expanded)
%              Depth                    :   39
%              Number of atoms          :  284 (461590 expanded)
%              Number of equality atoms :  154 (274769 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X20
        | X25 = X21
        | X25 = X22
        | X25 = X23
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X20
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X21
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X22
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X27
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | esk2_5(X27,X28,X29,X30,X31) = X27
        | esk2_5(X27,X28,X29,X30,X31) = X28
        | esk2_5(X27,X28,X29,X30,X31) = X29
        | esk2_5(X27,X28,X29,X30,X31) = X30
        | X31 = k2_enumset1(X27,X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X38,X39,X40,X42] :
      ( ( r2_hidden(esk3_3(X34,X35,X36),k1_relat_1(X34))
        | ~ r2_hidden(X36,X35)
        | X35 != k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( X36 = k1_funct_1(X34,esk3_3(X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | X35 != k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(X39,k1_relat_1(X34))
        | X38 != k1_funct_1(X34,X39)
        | r2_hidden(X38,X35)
        | X35 != k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(esk4_2(X34,X40),X40)
        | ~ r2_hidden(X42,k1_relat_1(X34))
        | esk4_2(X34,X40) != k1_funct_1(X34,X42)
        | X40 = k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk5_2(X34,X40),k1_relat_1(X34))
        | r2_hidden(esk4_2(X34,X40),X40)
        | X40 = k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( esk4_2(X34,X40) = k1_funct_1(X34,esk5_2(X34,X40))
        | r2_hidden(esk4_2(X34,X40),X40)
        | X40 = k2_relat_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X5,X6,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( r2_hidden(esk1_2(X17,X18),X17)
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 )
      & ( esk1_2(X17,X18) != X18
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | X3 != k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X4,X5,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk7_0) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_14])).

cnf(c_0_29,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | X1 != k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X4,X5,X6)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24]),c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | X2 = X3
    | r2_hidden(esk1_2(X1,X3),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(esk7_0) != k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_22]),c_0_23]),c_0_24]),c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = X1
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])).

cnf(c_0_48,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk6_0
    | X2 != k1_relat_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_33])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_33])])).

cnf(c_0_53,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))) = esk1_2(k2_relat_1(esk7_0),X1)
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)) = esk6_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_58,plain,(
    ! [X33] :
      ( ( k1_relat_1(X33) != k1_xboole_0
        | k2_relat_1(X33) = k1_xboole_0
        | ~ v1_relat_1(X33) )
      & ( k2_relat_1(X33) != k1_xboole_0
        | k1_relat_1(X33) = k1_xboole_0
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_22]),c_0_23]),c_0_24]),c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),X1) = k1_funct_1(esk7_0,esk6_0)
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)
    | k1_funct_1(esk7_0,esk6_0) != X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_33])])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),X2),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))) = esk1_2(k2_relat_1(esk7_0),X1)
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)) = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),X1) = k1_funct_1(esk7_0,esk6_0)
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0))
    | k1_funct_1(esk7_0,esk6_0) != X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_43])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_74]),c_0_33])])).

cnf(c_0_76,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_82]),c_0_82]),c_0_82]),c_0_82]),c_0_82]),c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_47]),c_0_63])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),X1) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_84]),c_0_86]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | esk6_0 != X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_88]),c_0_28]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_89]),c_0_33])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_89]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.63  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.48/0.63  # and selection function SelectNegativeLiterals.
% 0.48/0.63  #
% 0.48/0.63  # Preprocessing time       : 0.028 s
% 0.48/0.63  # Presaturation interreduction done
% 0.48/0.63  
% 0.48/0.63  # Proof found!
% 0.48/0.63  # SZS status Theorem
% 0.48/0.63  # SZS output start CNFRefutation
% 0.48/0.63  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.48/0.63  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.63  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.48/0.63  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.48/0.63  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.63  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.63  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.48/0.63  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.48/0.63  fof(c_0_9, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X25,X24)|(X25=X20|X25=X21|X25=X22|X25=X23)|X24!=k2_enumset1(X20,X21,X22,X23))&((((X26!=X20|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))&(X26!=X21|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X22|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X23|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))))&(((((esk2_5(X27,X28,X29,X30,X31)!=X27|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30))&(esk2_5(X27,X28,X29,X30,X31)!=X28|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk2_5(X27,X28,X29,X30,X31)!=X29|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk2_5(X27,X28,X29,X30,X31)!=X30|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|(esk2_5(X27,X28,X29,X30,X31)=X27|esk2_5(X27,X28,X29,X30,X31)=X28|esk2_5(X27,X28,X29,X30,X31)=X29|esk2_5(X27,X28,X29,X30,X31)=X30)|X31=k2_enumset1(X27,X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.48/0.63  fof(c_0_10, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.63  fof(c_0_11, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.48/0.63  fof(c_0_12, plain, ![X34, X35, X36, X38, X39, X40, X42]:((((r2_hidden(esk3_3(X34,X35,X36),k1_relat_1(X34))|~r2_hidden(X36,X35)|X35!=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(X36=k1_funct_1(X34,esk3_3(X34,X35,X36))|~r2_hidden(X36,X35)|X35!=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(~r2_hidden(X39,k1_relat_1(X34))|X38!=k1_funct_1(X34,X39)|r2_hidden(X38,X35)|X35!=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&((~r2_hidden(esk4_2(X34,X40),X40)|(~r2_hidden(X42,k1_relat_1(X34))|esk4_2(X34,X40)!=k1_funct_1(X34,X42))|X40=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&((r2_hidden(esk5_2(X34,X40),k1_relat_1(X34))|r2_hidden(esk4_2(X34,X40),X40)|X40=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(esk4_2(X34,X40)=k1_funct_1(X34,esk5_2(X34,X40))|r2_hidden(esk4_2(X34,X40),X40)|X40=k2_relat_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.48/0.63  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.48/0.63  cnf(c_0_14, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.48/0.63  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.48/0.63  fof(c_0_16, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.63  fof(c_0_17, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.63  fof(c_0_18, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.63  cnf(c_0_19, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.63  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X5,X6,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.48/0.63  cnf(c_0_21, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.63  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.63  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.63  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.63  fof(c_0_25, plain, ![X17, X18]:((r2_hidden(esk1_2(X17,X18),X17)|(X17=k1_tarski(X18)|X17=k1_xboole_0))&(esk1_2(X17,X18)!=X18|(X17=k1_tarski(X18)|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.48/0.63  cnf(c_0_26, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|X3!=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[c_0_19])).
% 0.48/0.63  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X4,X5,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.48/0.63  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk7_0)=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_14])).
% 0.48/0.63  cnf(c_0_29, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.48/0.63  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.63  cnf(c_0_31, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[c_0_26])).
% 0.48/0.63  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.63  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.63  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,X1)|X1!=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.63  cnf(c_0_35, plain, (X1=X6|X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X4,X5,X6)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_14])).
% 0.48/0.63  cnf(c_0_36, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24]), c_0_14])).
% 0.48/0.63  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.48/0.63  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(er,[status(thm)],[c_0_34])).
% 0.48/0.63  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.63  cnf(c_0_40, plain, (X1=k1_xboole_0|X2=X3|r2_hidden(esk1_2(X1,X3),X1)|~r2_hidden(X2,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36])])).
% 0.48/0.63  cnf(c_0_41, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.48/0.63  cnf(c_0_42, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.63  cnf(c_0_43, negated_conjecture, (k2_relat_1(esk7_0)!=k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_22]), c_0_23]), c_0_24]), c_0_14])).
% 0.48/0.63  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=X1|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.48/0.63  cnf(c_0_45, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.63  cnf(c_0_46, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_42])).
% 0.48/0.63  cnf(c_0_47, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36])).
% 0.48/0.63  cnf(c_0_48, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_45])).
% 0.48/0.63  cnf(c_0_49, negated_conjecture, (X1=esk6_0|X2!=k1_relat_1(esk7_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.48/0.63  cnf(c_0_50, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_33])])).
% 0.48/0.63  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 0.48/0.63  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_32]), c_0_33])])).
% 0.48/0.63  cnf(c_0_53, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(er,[status(thm)],[c_0_49])).
% 0.48/0.63  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.63  cnf(c_0_55, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.63  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)))=esk1_2(k2_relat_1(esk7_0),X1)|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.48/0.63  cnf(c_0_57, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))=esk6_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.48/0.63  fof(c_0_58, plain, ![X33]:((k1_relat_1(X33)!=k1_xboole_0|k2_relat_1(X33)=k1_xboole_0|~v1_relat_1(X33))&(k2_relat_1(X33)!=k1_xboole_0|k1_relat_1(X33)=k1_xboole_0|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.48/0.63  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_22]), c_0_23]), c_0_24]), c_0_14])).
% 0.48/0.63  cnf(c_0_60, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),X1)=k1_funct_1(esk7_0,esk6_0)|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.48/0.63  cnf(c_0_61, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.48/0.63  cnf(c_0_62, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)|k1_funct_1(esk7_0,esk6_0)!=X1), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.48/0.63  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_33])])).
% 0.48/0.63  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_62]), c_0_43])).
% 0.48/0.63  cnf(c_0_65, negated_conjecture, (X1=esk6_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),X2),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_63])).
% 0.48/0.63  cnf(c_0_66, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_64])).
% 0.48/0.63  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.48/0.63  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_67])).
% 0.48/0.63  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_68])).
% 0.48/0.63  cnf(c_0_70, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)))=esk1_2(k2_relat_1(esk7_0),X1)|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_52, c_0_68])).
% 0.48/0.63  cnf(c_0_71, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_53, c_0_69])).
% 0.48/0.63  cnf(c_0_72, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),X1)=k1_funct_1(esk7_0,esk6_0)|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.48/0.63  cnf(c_0_73, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))|k1_funct_1(esk7_0,esk6_0)!=X1), inference(spm,[status(thm)],[c_0_59, c_0_72])).
% 0.48/0.63  cnf(c_0_74, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_43])).
% 0.48/0.63  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_74]), c_0_33])])).
% 0.48/0.63  cnf(c_0_76, negated_conjecture, (X1=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_75])).
% 0.48/0.63  cnf(c_0_77, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_76, c_0_66])).
% 0.48/0.63  cnf(c_0_78, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_77])).
% 0.48/0.63  cnf(c_0_79, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_78])).
% 0.48/0.63  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_52, c_0_78])).
% 0.48/0.63  cnf(c_0_81, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_53, c_0_79])).
% 0.48/0.63  cnf(c_0_82, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.48/0.63  cnf(c_0_83, negated_conjecture, (k2_relat_1(esk7_0)!=k1_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_82]), c_0_82]), c_0_82]), c_0_82]), c_0_82]), c_0_28])).
% 0.48/0.63  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_47]), c_0_63])).
% 0.48/0.63  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_84])).
% 0.48/0.63  cnf(c_0_86, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))=esk6_0), inference(spm,[status(thm)],[c_0_53, c_0_85])).
% 0.48/0.63  cnf(c_0_87, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),X1)=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_84]), c_0_86]), c_0_82])).
% 0.48/0.63  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|esk6_0!=X1), inference(spm,[status(thm)],[c_0_59, c_0_87])).
% 0.48/0.63  cnf(c_0_89, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_88]), c_0_28]), c_0_83])).
% 0.48/0.63  cnf(c_0_90, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_89]), c_0_33])])).
% 0.48/0.63  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_89]), c_0_90])]), ['proof']).
% 0.48/0.63  # SZS output end CNFRefutation
% 0.48/0.63  # Proof object total steps             : 92
% 0.48/0.63  # Proof object clause steps            : 73
% 0.48/0.63  # Proof object formula steps           : 19
% 0.48/0.63  # Proof object conjectures             : 54
% 0.48/0.63  # Proof object clause conjectures      : 51
% 0.48/0.63  # Proof object formula conjectures     : 3
% 0.48/0.63  # Proof object initial clauses used    : 16
% 0.48/0.63  # Proof object initial formulas used   : 9
% 0.48/0.63  # Proof object generating inferences   : 47
% 0.48/0.63  # Proof object simplifying inferences  : 50
% 0.48/0.63  # Training examples: 0 positive, 0 negative
% 0.48/0.63  # Parsed axioms                        : 9
% 0.48/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.63  # Initial clauses                      : 28
% 0.48/0.63  # Removed in clause preprocessing      : 4
% 0.48/0.63  # Initial clauses in saturation        : 24
% 0.48/0.63  # Processed clauses                    : 728
% 0.48/0.63  # ...of these trivial                  : 15
% 0.48/0.63  # ...subsumed                          : 224
% 0.48/0.63  # ...remaining for further processing  : 488
% 0.48/0.63  # Other redundant clauses eliminated   : 590
% 0.48/0.63  # Clauses deleted for lack of memory   : 0
% 0.48/0.63  # Backward-subsumed                    : 114
% 0.48/0.63  # Backward-rewritten                   : 225
% 0.48/0.63  # Generated clauses                    : 25203
% 0.48/0.63  # ...of the previous two non-trivial   : 22626
% 0.48/0.63  # Contextual simplify-reflections      : 17
% 0.48/0.63  # Paramodulations                      : 24447
% 0.48/0.63  # Factorizations                       : 84
% 0.48/0.63  # Equation resolutions                 : 672
% 0.48/0.63  # Propositional unsat checks           : 0
% 0.48/0.63  #    Propositional check models        : 0
% 0.48/0.63  #    Propositional check unsatisfiable : 0
% 0.48/0.63  #    Propositional clauses             : 0
% 0.48/0.63  #    Propositional clauses after purity: 0
% 0.48/0.63  #    Propositional unsat core size     : 0
% 0.48/0.63  #    Propositional preprocessing time  : 0.000
% 0.48/0.63  #    Propositional encoding time       : 0.000
% 0.48/0.63  #    Propositional solver time         : 0.000
% 0.48/0.63  #    Success case prop preproc time    : 0.000
% 0.48/0.63  #    Success case prop encoding time   : 0.000
% 0.48/0.63  #    Success case prop solver time     : 0.000
% 0.48/0.63  # Current number of processed clauses  : 121
% 0.48/0.63  #    Positive orientable unit clauses  : 11
% 0.48/0.63  #    Positive unorientable unit clauses: 0
% 0.48/0.63  #    Negative unit clauses             : 0
% 0.48/0.63  #    Non-unit-clauses                  : 110
% 0.48/0.63  # Current number of unprocessed clauses: 21834
% 0.48/0.63  # ...number of literals in the above   : 119235
% 0.48/0.63  # Current number of archived formulas  : 0
% 0.48/0.63  # Current number of archived clauses   : 367
% 0.48/0.63  # Clause-clause subsumption calls (NU) : 26600
% 0.48/0.63  # Rec. Clause-clause subsumption calls : 7186
% 0.48/0.63  # Non-unit clause-clause subsumptions  : 334
% 0.48/0.63  # Unit Clause-clause subsumption calls : 1604
% 0.48/0.63  # Rewrite failures with RHS unbound    : 0
% 0.48/0.63  # BW rewrite match attempts            : 35
% 0.48/0.63  # BW rewrite match successes           : 13
% 0.48/0.63  # Condensation attempts                : 0
% 0.48/0.63  # Condensation successes               : 0
% 0.48/0.63  # Termbank termtop insertions          : 425598
% 0.48/0.63  
% 0.48/0.63  # -------------------------------------------------
% 0.48/0.63  # User time                : 0.270 s
% 0.48/0.63  # System time              : 0.012 s
% 0.48/0.63  # Total time               : 0.282 s
% 0.48/0.63  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
