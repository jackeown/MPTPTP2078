%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  91 expanded)
%              Number of clauses        :   23 (  37 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 262 expanded)
%              Number of equality atoms :   20 (  64 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(k4_tarski(X19,X20),X21)
        | r2_hidden(X20,k11_relat_1(X21,X19))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X20,k11_relat_1(X21,X19))
        | r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_10,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(X23,k2_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_16,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_xboole_0(k2_tarski(X10,X11),X12)
      | ~ r2_hidden(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k10_relat_1(X18,k2_relat_1(X18)) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk4_0,X1))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7] : r1_xboole_0(X7,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_26,plain,(
    ! [X13,X14,X15,X17] :
      ( ( r2_hidden(esk2_3(X13,X14,X15),k2_relat_1(X15))
        | ~ r2_hidden(X13,k10_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(X13,esk2_3(X13,X14,X15)),X15)
        | ~ r2_hidden(X13,k10_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X14)
        | ~ r2_hidden(X13,k10_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X17,k2_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X17),X15)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X13,k10_relat_1(X15,X14))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k1_enumset1(X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
    | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,X1),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_17])]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03FN
% 0.20/0.38  # and selection function PSelectLComplex.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.20/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.38  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.20/0.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.20/0.38  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.38  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.38  fof(c_0_9, plain, ![X19, X20, X21]:((~r2_hidden(k4_tarski(X19,X20),X21)|r2_hidden(X20,k11_relat_1(X21,X19))|~v1_relat_1(X21))&(~r2_hidden(X20,k11_relat_1(X21,X19))|r2_hidden(k4_tarski(X19,X20),X21)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.20/0.38  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_14, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0)&(r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X22, X23, X24]:((r2_hidden(X22,k1_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))&(r2_hidden(X23,k2_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.20/0.38  cnf(c_0_16, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_18, plain, ![X10, X11, X12]:(~r1_xboole_0(k2_tarski(X10,X11),X12)|~r2_hidden(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.20/0.38  fof(c_0_19, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_20, plain, ![X18]:(~v1_relat_1(X18)|k10_relat_1(X18,k2_relat_1(X18))=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k11_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk4_0,X1))),esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_23, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_25, plain, ![X7]:r1_xboole_0(X7,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.38  fof(c_0_26, plain, ![X13, X14, X15, X17]:((((r2_hidden(esk2_3(X13,X14,X15),k2_relat_1(X15))|~r2_hidden(X13,k10_relat_1(X15,X14))|~v1_relat_1(X15))&(r2_hidden(k4_tarski(X13,esk2_3(X13,X14,X15)),X15)|~r2_hidden(X13,k10_relat_1(X15,X14))|~v1_relat_1(X15)))&(r2_hidden(esk2_3(X13,X14,X15),X14)|~r2_hidden(X13,k10_relat_1(X15,X14))|~v1_relat_1(X15)))&(~r2_hidden(X17,k2_relat_1(X15))|~r2_hidden(k4_tarski(X13,X17),X15)|~r2_hidden(X17,X14)|r2_hidden(X13,k10_relat_1(X15,X14))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.38  cnf(c_0_27, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k11_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.20/0.38  cnf(c_0_30, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k1_enumset1(X1,X1,X2),X3)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk4_0,k2_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_17])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,X1),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_17])]), c_0_37])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 42
% 0.20/0.38  # Proof object clause steps            : 23
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 14
% 0.20/0.38  # Proof object clause conjectures      : 11
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 9
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 16
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 45
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 43
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 35
% 0.20/0.38  # ...of the previous two non-trivial   : 34
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 35
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 26
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 19
% 0.20/0.38  # Current number of unprocessed clauses: 18
% 0.20/0.38  # ...number of literals in the above   : 48
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 18
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 57
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 36
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1833
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
