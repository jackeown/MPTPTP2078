%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:04 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   71 (1191 expanded)
%              Number of clauses        :   52 ( 461 expanded)
%              Number of leaves         :    9 ( 303 expanded)
%              Depth                    :   18
%              Number of atoms          :  235 (5193 expanded)
%              Number of equality atoms :   77 (2292 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & k1_relat_1(esk8_0) = k1_relat_1(esk9_0)
    & k2_relat_1(esk8_0) = k1_tarski(esk7_0)
    & k2_relat_1(esk9_0) = k1_tarski(esk7_0)
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(esk9_0) = k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_relat_1(esk8_0) = k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk8_0) = k2_relat_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X31,X32,X33,X35] :
      ( ( r2_hidden(esk4_3(X27,X28,X29),k1_relat_1(X27))
        | ~ r2_hidden(X29,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X29 = k1_funct_1(X27,esk4_3(X27,X28,X29))
        | ~ r2_hidden(X29,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X32,k1_relat_1(X27))
        | X31 != k1_funct_1(X27,X32)
        | r2_hidden(X31,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(esk5_2(X27,X33),X33)
        | ~ r2_hidden(X35,k1_relat_1(X27))
        | esk5_2(X27,X33) != k1_funct_1(X27,X35)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(esk6_2(X27,X33),k1_relat_1(X27))
        | r2_hidden(esk5_2(X27,X33),X33)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( esk5_2(X27,X33) = k1_funct_1(X27,esk6_2(X27,X33))
        | r2_hidden(esk5_2(X27,X33),X33)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_26,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,k1_relat_1(X39))
        | ~ r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( X38 = k1_funct_1(X39,X37)
        | ~ r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( ~ r2_hidden(X37,k1_relat_1(X39))
        | X38 != k1_funct_1(X39,X37)
        | r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_35,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(k4_tarski(X22,X23),X20)
        | r2_hidden(k4_tarski(X22,X23),X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X20)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X24)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),X2)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0))
    | ~ r1_tarski(esk9_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk9_0,X1),esk3_2(esk9_0,X1)),esk9_0)
    | r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(X1,X2) = esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(esk9_0))
    | ~ r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk9_0,esk2_2(esk9_0,X1)) = esk3_2(esk9_0,X1)
    | r1_tarski(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_44]),c_0_33]),c_0_34])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,X1),k1_relat_1(esk9_0))
    | r1_tarski(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_33]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( esk3_2(esk9_0,X1) = esk7_0
    | r1_tarski(esk9_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_33]),c_0_34]),c_0_52])]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk3_2(esk8_0,X1)),esk8_0)
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ r2_hidden(k4_tarski(esk2_2(esk9_0,X1),esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_34])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_57]),c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk8_0,esk2_2(esk8_0,X1)) = esk3_2(esk8_0,X1)
    | r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_58]),c_0_47]),c_0_48])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(esk8_0,X1),k1_relat_1(esk9_0))
    | r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_49]),c_0_47]),c_0_48])])).

cnf(c_0_64,negated_conjecture,
    ( esk3_2(esk8_0,X1) = esk7_0
    | r1_tarski(esk8_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_61]),c_0_47]),c_0_48]),c_0_62])]),c_0_63])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | ~ r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_64]),c_0_48])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_39]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_63]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:38:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.028 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t17_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 0.18/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.18/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.38  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.18/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3)))), inference(assume_negation,[status(cth)],[t17_funct_1])).
% 0.18/0.38  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&(((k1_relat_1(esk8_0)=k1_relat_1(esk9_0)&k2_relat_1(esk8_0)=k1_tarski(esk7_0))&k2_relat_1(esk9_0)=k1_tarski(esk7_0))&esk8_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.38  fof(c_0_11, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.38  fof(c_0_12, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.38  fof(c_0_13, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.38  fof(c_0_14, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.38  cnf(c_0_15, negated_conjecture, (k2_relat_1(esk9_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_19, negated_conjecture, (k2_relat_1(esk8_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_20, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (k2_relat_1(esk9_0)=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.18/0.38  cnf(c_0_22, negated_conjecture, (k2_relat_1(esk8_0)=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17]), c_0_18])).
% 0.18/0.38  cnf(c_0_23, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_16]), c_0_17]), c_0_18])).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk8_0)=k2_relat_1(esk9_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.38  fof(c_0_25, plain, ![X27, X28, X29, X31, X32, X33, X35]:((((r2_hidden(esk4_3(X27,X28,X29),k1_relat_1(X27))|~r2_hidden(X29,X28)|X28!=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X29=k1_funct_1(X27,esk4_3(X27,X28,X29))|~r2_hidden(X29,X28)|X28!=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X32,k1_relat_1(X27))|X31!=k1_funct_1(X27,X32)|r2_hidden(X31,X28)|X28!=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&((~r2_hidden(esk5_2(X27,X33),X33)|(~r2_hidden(X35,k1_relat_1(X27))|esk5_2(X27,X33)!=k1_funct_1(X27,X35))|X33=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&((r2_hidden(esk6_2(X27,X33),k1_relat_1(X27))|r2_hidden(esk5_2(X27,X33),X33)|X33=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(esk5_2(X27,X33)=k1_funct_1(X27,esk6_2(X27,X33))|r2_hidden(esk5_2(X27,X33),X33)|X33=k2_relat_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.18/0.38  fof(c_0_26, plain, ![X37, X38, X39]:(((r2_hidden(X37,k1_relat_1(X39))|~r2_hidden(k4_tarski(X37,X38),X39)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(X38=k1_funct_1(X39,X37)|~r2_hidden(k4_tarski(X37,X38),X39)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(~r2_hidden(X37,k1_relat_1(X39))|X38!=k1_funct_1(X39,X37)|r2_hidden(k4_tarski(X37,X38),X39)|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.38  cnf(c_0_27, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_28, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)), inference(rw,[status(thm)],[c_0_22, c_0_24])).
% 0.18/0.38  cnf(c_0_29, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_31, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.38  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  fof(c_0_35, plain, ![X20, X21, X22, X23, X24]:((~r1_tarski(X20,X21)|(~r2_hidden(k4_tarski(X22,X23),X20)|r2_hidden(k4_tarski(X22,X23),X21))|~v1_relat_1(X20))&((r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X20)|r1_tarski(X20,X24)|~v1_relat_1(X20))&(~r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X24)|r1_tarski(X20,X24)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.18/0.38  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk9_0,X1)=esk7_0|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.18/0.38  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),esk9_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33]), c_0_34])])).
% 0.18/0.38  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.38  fof(c_0_41, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.38  cnf(c_0_42, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),X2)|~r2_hidden(X1,k1_relat_1(esk9_0))|~r1_tarski(esk9_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk9_0,X1),esk3_2(esk9_0,X1)),esk9_0)|r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.18/0.38  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.38  cnf(c_0_46, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk8_0)=k1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_50, negated_conjecture, (k1_funct_1(X1,X2)=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(esk9_0))|~r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk9_0,esk2_2(esk9_0,X1))=esk3_2(esk9_0,X1)|r1_tarski(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_44]), c_0_33]), c_0_34])])).
% 0.18/0.38  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_2(esk9_0,X1),k1_relat_1(esk9_0))|r1_tarski(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_33]), c_0_34])])).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk9_0))|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_47]), c_0_48]), c_0_49])])).
% 0.18/0.38  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.38  cnf(c_0_56, negated_conjecture, (esk3_2(esk9_0,X1)=esk7_0|r1_tarski(esk9_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_33]), c_0_34]), c_0_52])]), c_0_53])).
% 0.18/0.38  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk8_0,X1)=esk7_0|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_31, c_0_54])).
% 0.18/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk3_2(esk8_0,X1)),esk8_0)|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk9_0,X1)|~r2_hidden(k4_tarski(esk2_2(esk9_0,X1),esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_34])])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),esk8_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_57]), c_0_47]), c_0_48]), c_0_49])])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk8_0,esk2_2(esk8_0,X1))=esk3_2(esk8_0,X1)|r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_58]), c_0_47]), c_0_48])])).
% 0.18/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_53])).
% 0.18/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_2(esk8_0,X1),k1_relat_1(esk9_0))|r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_58]), c_0_49]), c_0_47]), c_0_48])])).
% 0.18/0.38  cnf(c_0_64, negated_conjecture, (esk3_2(esk8_0,X1)=esk7_0|r1_tarski(esk8_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_61]), c_0_47]), c_0_48]), c_0_62])]), c_0_63])).
% 0.18/0.38  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.38  cnf(c_0_66, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk8_0,X1)|~r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_64]), c_0_48])])).
% 0.18/0.38  cnf(c_0_68, negated_conjecture, (~r1_tarski(esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_66])).
% 0.18/0.38  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk2_2(esk8_0,esk9_0),k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_39]), c_0_68])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_63]), c_0_68]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 71
% 0.18/0.38  # Proof object clause steps            : 52
% 0.18/0.38  # Proof object formula steps           : 19
% 0.18/0.38  # Proof object conjectures             : 37
% 0.18/0.38  # Proof object clause conjectures      : 34
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 21
% 0.18/0.38  # Proof object initial formulas used   : 9
% 0.18/0.38  # Proof object generating inferences   : 22
% 0.18/0.38  # Proof object simplifying inferences  : 63
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 9
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 30
% 0.18/0.38  # Removed in clause preprocessing      : 3
% 0.18/0.38  # Initial clauses in saturation        : 27
% 0.18/0.38  # Processed clauses                    : 163
% 0.18/0.38  # ...of these trivial                  : 0
% 0.18/0.38  # ...subsumed                          : 31
% 0.18/0.38  # ...remaining for further processing  : 132
% 0.18/0.38  # Other redundant clauses eliminated   : 14
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 4
% 0.18/0.38  # Backward-rewritten                   : 1
% 0.18/0.38  # Generated clauses                    : 442
% 0.18/0.38  # ...of the previous two non-trivial   : 391
% 0.18/0.38  # Contextual simplify-reflections      : 8
% 0.18/0.38  # Paramodulations                      : 428
% 0.18/0.38  # Factorizations                       : 2
% 0.18/0.38  # Equation resolutions                 : 14
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 93
% 0.18/0.38  #    Positive orientable unit clauses  : 11
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 3
% 0.18/0.38  #    Non-unit-clauses                  : 79
% 0.18/0.38  # Current number of unprocessed clauses: 260
% 0.18/0.38  # ...number of literals in the above   : 1346
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 34
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 2278
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 420
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 42
% 0.18/0.38  # Unit Clause-clause subsumption calls : 32
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 3
% 0.18/0.38  # BW rewrite match successes           : 1
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 10694
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.042 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.048 s
% 0.18/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
