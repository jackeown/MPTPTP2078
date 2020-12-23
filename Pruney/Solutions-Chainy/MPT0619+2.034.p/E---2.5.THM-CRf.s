%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:55 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   95 (144223 expanded)
%              Number of clauses        :   75 (62464 expanded)
%              Number of leaves         :   10 (37253 expanded)
%              Depth                    :   39
%              Number of atoms          :  278 (443134 expanded)
%              Number of equality atoms :  150 (262019 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_10,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X6
        | X10 = X7
        | X10 = X8
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X6
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( esk1_4(X12,X13,X14,X15) != X12
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X13
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X14
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | esk1_4(X12,X13,X14,X15) = X12
        | esk1_4(X12,X13,X14,X15) = X13
        | esk1_4(X12,X13,X14,X15) = X14
        | X15 = k1_enumset1(X12,X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_14,plain,(
    ! [X31,X32,X33,X35,X36,X37,X39] :
      ( ( r2_hidden(esk3_3(X31,X32,X33),k1_relat_1(X31))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( X33 = k1_funct_1(X31,esk3_3(X31,X32,X33))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X36,k1_relat_1(X31))
        | X35 != k1_funct_1(X31,X36)
        | r2_hidden(X35,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(esk4_2(X31,X37),X37)
        | ~ r2_hidden(X39,k1_relat_1(X31))
        | esk4_2(X31,X37) != k1_funct_1(X31,X39)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( r2_hidden(esk5_2(X31,X37),k1_relat_1(X31))
        | r2_hidden(esk4_2(X31,X37),X37)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( esk4_2(X31,X37) = k1_funct_1(X31,esk5_2(X31,X37))
        | r2_hidden(esk4_2(X31,X37),X37)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X27,X28] :
      ( ( r2_hidden(esk2_2(X27,X28),X27)
        | X27 = k1_tarski(X28)
        | X27 = k1_xboole_0 )
      & ( esk2_2(X27,X28) != X28
        | X27 = k1_tarski(X28)
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | X3 != k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk7_0) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_16]),c_0_17])).

cnf(c_0_30,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | X1 != k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_17])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_16]),c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = X3
    | r2_hidden(esk2_2(X1,X3),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk7_0) != k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_25]),c_0_16]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = X1
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])).

cnf(c_0_49,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk6_0
    | X2 != k1_relat_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_33]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))) = esk2_2(k2_relat_1(esk7_0),X1)
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)) = esk6_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X30] :
      ( ( k1_relat_1(X30) != k1_xboole_0
        | X30 = k1_xboole_0
        | ~ v1_relat_1(X30) )
      & ( k2_relat_1(X30) != k1_xboole_0
        | X30 = k1_xboole_0
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_24]),c_0_25]),c_0_16]),c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( esk2_2(k2_relat_1(esk7_0),X1) = k1_funct_1(esk7_0,esk6_0)
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)
    | k1_funct_1(esk7_0,esk6_0) != X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_34])])).

cnf(c_0_65,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_63]),c_0_44])).

cnf(c_0_67,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),X2),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))) = esk2_2(k2_relat_1(esk7_0),X1)
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)) = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk2_2(k2_relat_1(esk7_0),X1) = k1_funct_1(esk7_0,esk6_0)
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0))
    | k1_funct_1(esk7_0,esk6_0) != X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_75]),c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_76]),c_0_34])])).

cnf(c_0_78,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_77]),c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0
    | r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_29])).

cnf(c_0_86,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_64]),c_0_86]),c_0_65])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( esk2_2(k2_relat_1(esk7_0),X1) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_87]),c_0_89]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk7_0) = k3_enumset1(X1,X1,X1,X1,X1)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | esk6_0 != X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_91]),c_0_29]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_92]),c_0_34])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_92]),c_0_93]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:51:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.81  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.60/0.81  # and selection function SelectNegativeLiterals.
% 0.60/0.81  #
% 0.60/0.81  # Preprocessing time       : 0.028 s
% 0.60/0.81  # Presaturation interreduction done
% 0.60/0.81  
% 0.60/0.81  # Proof found!
% 0.60/0.81  # SZS status Theorem
% 0.60/0.81  # SZS output start CNFRefutation
% 0.60/0.81  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.60/0.81  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.60/0.81  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.60/0.81  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.60/0.81  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.60/0.81  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.60/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.60/0.81  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.60/0.81  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.60/0.81  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.60/0.81  fof(c_0_10, plain, ![X6, X7, X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X10,X9)|(X10=X6|X10=X7|X10=X8)|X9!=k1_enumset1(X6,X7,X8))&(((X11!=X6|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))&(X11!=X7|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8)))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))))&((((esk1_4(X12,X13,X14,X15)!=X12|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14))&(esk1_4(X12,X13,X14,X15)!=X13|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(esk1_4(X12,X13,X14,X15)!=X14|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(r2_hidden(esk1_4(X12,X13,X14,X15),X15)|(esk1_4(X12,X13,X14,X15)=X12|esk1_4(X12,X13,X14,X15)=X13|esk1_4(X12,X13,X14,X15)=X14)|X15=k1_enumset1(X12,X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.60/0.81  fof(c_0_11, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.60/0.81  fof(c_0_12, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.60/0.81  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.60/0.81  fof(c_0_14, plain, ![X31, X32, X33, X35, X36, X37, X39]:((((r2_hidden(esk3_3(X31,X32,X33),k1_relat_1(X31))|~r2_hidden(X33,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(X33=k1_funct_1(X31,esk3_3(X31,X32,X33))|~r2_hidden(X33,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X36,k1_relat_1(X31))|X35!=k1_funct_1(X31,X36)|r2_hidden(X35,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&((~r2_hidden(esk4_2(X31,X37),X37)|(~r2_hidden(X39,k1_relat_1(X31))|esk4_2(X31,X37)!=k1_funct_1(X31,X39))|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&((r2_hidden(esk5_2(X31,X37),k1_relat_1(X31))|r2_hidden(esk4_2(X31,X37),X37)|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(esk4_2(X31,X37)=k1_funct_1(X31,esk5_2(X31,X37))|r2_hidden(esk4_2(X31,X37),X37)|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.60/0.81  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.81  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.81  cnf(c_0_17, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.81  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.60/0.81  fof(c_0_19, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.60/0.81  fof(c_0_20, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.60/0.81  cnf(c_0_21, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.81  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_23, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.81  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.81  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.81  fof(c_0_26, plain, ![X27, X28]:((r2_hidden(esk2_2(X27,X28),X27)|(X27=k1_tarski(X28)|X27=k1_xboole_0))&(esk2_2(X27,X28)!=X28|(X27=k1_tarski(X28)|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.60/0.81  cnf(c_0_27, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|X3!=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_28, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.60/0.81  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk7_0)=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_30, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.81  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.81  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[c_0_27])).
% 0.60/0.81  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.81  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.81  cnf(c_0_35, negated_conjecture, (r2_hidden(esk6_0,X1)|X1!=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.60/0.81  cnf(c_0_36, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.60/0.81  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(er,[status(thm)],[c_0_35])).
% 0.60/0.81  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.81  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=X3|r2_hidden(esk2_2(X1,X3),X1)|~r2_hidden(X2,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37])])).
% 0.60/0.81  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.60/0.81  cnf(c_0_43, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.81  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk7_0)!=k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_25]), c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=X1|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.60/0.81  cnf(c_0_46, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.81  cnf(c_0_47, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_43])).
% 0.60/0.81  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])).
% 0.60/0.81  cnf(c_0_49, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_46])).
% 0.60/0.81  cnf(c_0_50, negated_conjecture, (X1=esk6_0|X2!=k1_relat_1(esk7_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 0.60/0.81  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_34])])).
% 0.60/0.81  cnf(c_0_52, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_48])).
% 0.60/0.81  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_33]), c_0_34])])).
% 0.60/0.81  cnf(c_0_54, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(er,[status(thm)],[c_0_50])).
% 0.60/0.81  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.60/0.81  cnf(c_0_56, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.81  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)))=esk2_2(k2_relat_1(esk7_0),X1)|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.60/0.81  cnf(c_0_58, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))=esk6_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.60/0.81  fof(c_0_59, plain, ![X30]:((k1_relat_1(X30)!=k1_xboole_0|X30=k1_xboole_0|~v1_relat_1(X30))&(k2_relat_1(X30)!=k1_xboole_0|X30=k1_xboole_0|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.60/0.81  cnf(c_0_60, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_24]), c_0_25]), c_0_16]), c_0_17])).
% 0.60/0.81  cnf(c_0_61, negated_conjecture, (esk2_2(k2_relat_1(esk7_0),X1)=k1_funct_1(esk7_0,esk6_0)|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.60/0.81  cnf(c_0_62, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.60/0.81  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)|k1_funct_1(esk7_0,esk6_0)!=X1), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.60/0.81  cnf(c_0_64, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_48]), c_0_34])])).
% 0.60/0.81  cnf(c_0_65, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.60/0.81  cnf(c_0_66, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_63]), c_0_44])).
% 0.60/0.81  cnf(c_0_67, negated_conjecture, (X1=esk6_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),X2),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_64]), c_0_65])).
% 0.60/0.81  cnf(c_0_68, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_66])).
% 0.60/0.81  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.60/0.81  cnf(c_0_70, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_69])).
% 0.60/0.81  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_70])).
% 0.60/0.81  cnf(c_0_72, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)))=esk2_2(k2_relat_1(esk7_0),X1)|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_53, c_0_70])).
% 0.60/0.81  cnf(c_0_73, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_71])).
% 0.60/0.81  cnf(c_0_74, negated_conjecture, (esk2_2(k2_relat_1(esk7_0),X1)=k1_funct_1(esk7_0,esk6_0)|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.60/0.81  cnf(c_0_75, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))|k1_funct_1(esk7_0,esk6_0)!=X1), inference(spm,[status(thm)],[c_0_60, c_0_74])).
% 0.60/0.81  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_75]), c_0_44])).
% 0.60/0.81  cnf(c_0_77, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_76]), c_0_34])])).
% 0.60/0.81  cnf(c_0_78, negated_conjecture, (X1=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_77]), c_0_65])).
% 0.60/0.81  cnf(c_0_79, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0|r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_78, c_0_68])).
% 0.60/0.81  cnf(c_0_80, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_79])).
% 0.60/0.81  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_80])).
% 0.60/0.81  cnf(c_0_82, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_53, c_0_80])).
% 0.60/0.81  cnf(c_0_83, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_54, c_0_81])).
% 0.60/0.81  cnf(c_0_84, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.60/0.81  cnf(c_0_85, negated_conjecture, (k2_relat_1(esk7_0)!=k1_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_29])).
% 0.60/0.81  cnf(c_0_86, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.60/0.81  cnf(c_0_87, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_64]), c_0_86]), c_0_65])])).
% 0.60/0.81  cnf(c_0_88, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_87])).
% 0.60/0.81  cnf(c_0_89, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))=esk6_0), inference(spm,[status(thm)],[c_0_54, c_0_88])).
% 0.60/0.81  cnf(c_0_90, negated_conjecture, (esk2_2(k2_relat_1(esk7_0),X1)=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_87]), c_0_89]), c_0_84])).
% 0.60/0.81  cnf(c_0_91, negated_conjecture, (k2_relat_1(esk7_0)=k3_enumset1(X1,X1,X1,X1,X1)|k2_relat_1(esk7_0)=k1_xboole_0|esk6_0!=X1), inference(spm,[status(thm)],[c_0_60, c_0_90])).
% 0.60/0.81  cnf(c_0_92, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_91]), c_0_29]), c_0_85])).
% 0.60/0.81  cnf(c_0_93, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_92]), c_0_34])])).
% 0.60/0.81  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_92]), c_0_93]), c_0_65])]), ['proof']).
% 0.60/0.81  # SZS output end CNFRefutation
% 0.60/0.81  # Proof object total steps             : 95
% 0.60/0.81  # Proof object clause steps            : 75
% 0.60/0.81  # Proof object formula steps           : 20
% 0.60/0.81  # Proof object conjectures             : 54
% 0.60/0.81  # Proof object clause conjectures      : 51
% 0.60/0.81  # Proof object formula conjectures     : 3
% 0.60/0.81  # Proof object initial clauses used    : 18
% 0.60/0.81  # Proof object initial formulas used   : 10
% 0.60/0.81  # Proof object generating inferences   : 47
% 0.60/0.81  # Proof object simplifying inferences  : 57
% 0.60/0.81  # Training examples: 0 positive, 0 negative
% 0.60/0.81  # Parsed axioms                        : 10
% 0.60/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.81  # Initial clauses                      : 28
% 0.60/0.81  # Removed in clause preprocessing      : 4
% 0.60/0.81  # Initial clauses in saturation        : 24
% 0.60/0.81  # Processed clauses                    : 980
% 0.60/0.81  # ...of these trivial                  : 20
% 0.60/0.81  # ...subsumed                          : 317
% 0.60/0.81  # ...remaining for further processing  : 642
% 0.60/0.81  # Other redundant clauses eliminated   : 1213
% 0.60/0.81  # Clauses deleted for lack of memory   : 0
% 0.60/0.81  # Backward-subsumed                    : 201
% 0.60/0.81  # Backward-rewritten                   : 345
% 0.60/0.81  # Generated clauses                    : 44561
% 0.60/0.81  # ...of the previous two non-trivial   : 37180
% 0.60/0.81  # Contextual simplify-reflections      : 12
% 0.60/0.81  # Paramodulations                      : 43160
% 0.60/0.81  # Factorizations                       : 67
% 0.60/0.81  # Equation resolutions                 : 1334
% 0.60/0.81  # Propositional unsat checks           : 0
% 0.60/0.81  #    Propositional check models        : 0
% 0.60/0.81  #    Propositional check unsatisfiable : 0
% 0.60/0.81  #    Propositional clauses             : 0
% 0.60/0.81  #    Propositional clauses after purity: 0
% 0.60/0.81  #    Propositional unsat core size     : 0
% 0.60/0.81  #    Propositional preprocessing time  : 0.000
% 0.60/0.81  #    Propositional encoding time       : 0.000
% 0.60/0.81  #    Propositional solver time         : 0.000
% 0.60/0.81  #    Success case prop preproc time    : 0.000
% 0.60/0.81  #    Success case prop encoding time   : 0.000
% 0.60/0.81  #    Success case prop solver time     : 0.000
% 0.60/0.81  # Current number of processed clauses  : 69
% 0.60/0.81  #    Positive orientable unit clauses  : 10
% 0.60/0.81  #    Positive unorientable unit clauses: 0
% 0.60/0.81  #    Negative unit clauses             : 0
% 0.60/0.81  #    Non-unit-clauses                  : 59
% 0.60/0.81  # Current number of unprocessed clauses: 35877
% 0.60/0.81  # ...number of literals in the above   : 209366
% 0.60/0.81  # Current number of archived formulas  : 0
% 0.60/0.81  # Current number of archived clauses   : 574
% 0.60/0.81  # Clause-clause subsumption calls (NU) : 43609
% 0.60/0.81  # Rec. Clause-clause subsumption calls : 8288
% 0.60/0.81  # Non-unit clause-clause subsumptions  : 509
% 0.60/0.81  # Unit Clause-clause subsumption calls : 2028
% 0.60/0.81  # Rewrite failures with RHS unbound    : 0
% 0.60/0.81  # BW rewrite match attempts            : 36
% 0.60/0.81  # BW rewrite match successes           : 15
% 0.60/0.81  # Condensation attempts                : 0
% 0.60/0.81  # Condensation successes               : 0
% 0.60/0.81  # Termbank termtop insertions          : 774147
% 0.60/0.81  
% 0.60/0.81  # -------------------------------------------------
% 0.60/0.81  # User time                : 0.447 s
% 0.60/0.81  # System time              : 0.025 s
% 0.60/0.81  # Total time               : 0.472 s
% 0.60/0.81  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
