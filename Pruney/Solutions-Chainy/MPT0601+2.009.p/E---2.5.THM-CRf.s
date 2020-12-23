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
% DateTime   : Thu Dec  3 10:52:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 148 expanded)
%              Number of clauses        :   24 (  68 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 379 expanded)
%              Number of equality atoms :   19 (  93 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_xboole_0(k2_tarski(X9,X10),X11)
      | ~ r2_hidden(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_8,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( ~ r2_hidden(esk8_0,k1_relat_1(esk9_0))
      | k11_relat_1(esk9_0,esk8_0) = k1_xboole_0 )
    & ( r2_hidden(esk8_0,k1_relat_1(esk9_0))
      | k11_relat_1(esk9_0,esk8_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(X24,esk4_3(X22,X23,X24)),X22)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),X22)
        | r2_hidden(X26,X23)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(esk5_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(esk5_2(X28,X29),X31),X28)
        | X29 = k1_relat_1(X28) )
      & ( r2_hidden(esk5_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk5_2(X28,X29),esk6_2(X28,X29)),X28)
        | X29 = k1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X5] : r1_xboole_0(X5,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk9_0))
    | k11_relat_1(esk9_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k1_enumset1(X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_hidden(k4_tarski(X39,X40),X41)
        | r2_hidden(X40,k11_relat_1(X41,X39))
        | ~ v1_relat_1(X41) )
      & ( ~ r2_hidden(X40,k11_relat_1(X41,X39))
        | r2_hidden(k4_tarski(X39,X40),X41)
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),esk6_2(X1,k11_relat_1(esk9_0,esk8_0))),X1)
    | r2_hidden(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk8_0,k1_relat_1(esk9_0))
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),esk6_2(X1,k11_relat_1(esk9_0,esk8_0))),X1)
    | r2_hidden(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))
    | r2_hidden(k4_tarski(esk5_2(X1,k1_xboole_0),esk6_2(X1,k1_xboole_0)),X1)
    | r2_hidden(esk8_0,k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15])]),c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(X2,k11_relat_1(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_2(k1_xboole_0,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk8_0,k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_23]),c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k11_relat_1(esk9_0,esk8_0) = k1_xboole_0
    | ~ r2_hidden(esk8_0,k1_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk9_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk4_3(esk9_0,k1_relat_1(esk9_0),esk8_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k11_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.14/0.38  # and selection function SelectCQIArEqFirst.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.14/0.38  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.14/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.14/0.38  fof(c_0_7, plain, ![X9, X10, X11]:(~r1_xboole_0(k2_tarski(X9,X10),X11)|~r2_hidden(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.14/0.38  fof(c_0_8, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, (v1_relat_1(esk9_0)&((~r2_hidden(esk8_0,k1_relat_1(esk9_0))|k11_relat_1(esk9_0,esk8_0)=k1_xboole_0)&(r2_hidden(esk8_0,k1_relat_1(esk9_0))|k11_relat_1(esk9_0,esk8_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(X24,esk4_3(X22,X23,X24)),X22)|X23!=k1_relat_1(X22))&(~r2_hidden(k4_tarski(X26,X27),X22)|r2_hidden(X26,X23)|X23!=k1_relat_1(X22)))&((~r2_hidden(esk5_2(X28,X29),X29)|~r2_hidden(k4_tarski(esk5_2(X28,X29),X31),X28)|X29=k1_relat_1(X28))&(r2_hidden(esk5_2(X28,X29),X29)|r2_hidden(k4_tarski(esk5_2(X28,X29),esk6_2(X28,X29)),X28)|X29=k1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.14/0.38  cnf(c_0_11, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_13, plain, ![X5]:r1_xboole_0(X5,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk9_0))|k11_relat_1(esk9_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k1_enumset1(X1,X1,X2),X3)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.38  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_18, plain, ![X39, X40, X41]:((~r2_hidden(k4_tarski(X39,X40),X41)|r2_hidden(X40,k11_relat_1(X41,X39))|~v1_relat_1(X41))&(~r2_hidden(X40,k11_relat_1(X41,X39))|r2_hidden(k4_tarski(X39,X40),X41)|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),esk6_2(X1,k11_relat_1(esk9_0,esk8_0))),X1)|r2_hidden(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))|r2_hidden(esk8_0,k1_relat_1(esk9_0))|k1_relat_1(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),esk6_2(X1,k11_relat_1(esk9_0,esk8_0))),X1)|r2_hidden(esk5_2(X1,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))|r2_hidden(k4_tarski(esk5_2(X1,k1_xboole_0),esk6_2(X1,k1_xboole_0)),X1)|r2_hidden(esk8_0,k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15])]), c_0_20])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk9_0)|~r2_hidden(X2,k11_relat_1(esk9_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk5_2(k1_xboole_0,k11_relat_1(esk9_0,esk8_0)),k11_relat_1(esk9_0,esk8_0))|r2_hidden(esk8_0,k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_23]), c_0_20])).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (k11_relat_1(esk9_0,esk8_0)=k1_xboole_0|~r2_hidden(esk8_0,k1_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk9_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk4_3(esk9_0,k1_relat_1(esk9_0),esk8_0)),esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k11_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31])])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_20]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 37
% 0.14/0.38  # Proof object clause steps            : 24
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 9
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 12
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 23
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 21
% 0.14/0.38  # Processed clauses                    : 91
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 14
% 0.14/0.38  # ...remaining for further processing  : 77
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 7
% 0.14/0.38  # Generated clauses                    : 128
% 0.14/0.38  # ...of the previous two non-trivial   : 122
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 125
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 3
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 47
% 0.14/0.38  #    Positive orientable unit clauses  : 8
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 38
% 0.14/0.38  # Current number of unprocessed clauses: 70
% 0.14/0.38  # ...number of literals in the above   : 311
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 30
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 488
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 226
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.38  # Unit Clause-clause subsumption calls : 8
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5222
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.036 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.039 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
