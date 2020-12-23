%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:24 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 145 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 299 expanded)
%              Number of equality atoms :   67 ( 156 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_12,plain,(
    ! [X45,X46] :
      ( r2_hidden(X45,X46)
      | r1_xboole_0(k1_tarski(X45),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X41,X42,X43,X44] : k3_enumset1(X41,X41,X42,X43,X44) = k2_enumset1(X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k4_xboole_0(X22,X23) = X22 )
      & ( k4_xboole_0(X22,X23) != X22
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_19,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,negated_conjecture,
    ( ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) != esk3_0
      | r2_hidden(esk4_0,esk3_0) )
    & ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = esk3_0
      | ~ r2_hidden(esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

fof(c_0_31,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X24
        | X28 = X25
        | X28 = X26
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X24
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( esk2_4(X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk2_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk2_4(X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk2_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk2_4(X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk2_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( r2_hidden(esk2_4(X30,X31,X32,X33),X33)
        | esk2_4(X30,X31,X32,X33) = X30
        | esk2_4(X30,X31,X32,X33) = X31
        | esk2_4(X30,X31,X32,X33) = X32
        | X33 = k1_enumset1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | k4_xboole_0(esk3_0,k1_tarski(esk4_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = esk3_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_28]),c_0_24]),c_0_25])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) = X1
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_25])).

fof(c_0_42,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X19)
        | r2_hidden(X17,X18)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_22]),c_0_23]),c_0_28]),c_0_24]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_52,c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.40/0.62  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.40/0.62  # and selection function SelectNegativeLiterals.
% 0.40/0.62  #
% 0.40/0.62  # Preprocessing time       : 0.040 s
% 0.40/0.62  # Presaturation interreduction done
% 0.40/0.62  
% 0.40/0.62  # Proof found!
% 0.40/0.62  # SZS status Theorem
% 0.40/0.62  # SZS output start CNFRefutation
% 0.40/0.62  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.40/0.62  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.40/0.62  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.40/0.62  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.40/0.62  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.40/0.62  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.40/0.62  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.40/0.62  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.40/0.62  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.40/0.62  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.40/0.62  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.40/0.62  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.40/0.62  fof(c_0_12, plain, ![X45, X46]:(r2_hidden(X45,X46)|r1_xboole_0(k1_tarski(X45),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.40/0.62  fof(c_0_13, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.40/0.62  fof(c_0_14, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.40/0.62  fof(c_0_15, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.40/0.62  fof(c_0_16, plain, ![X41, X42, X43, X44]:k3_enumset1(X41,X41,X42,X43,X44)=k2_enumset1(X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.40/0.62  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.40/0.62  fof(c_0_18, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k4_xboole_0(X22,X23)=X22)&(k4_xboole_0(X22,X23)!=X22|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.40/0.62  fof(c_0_19, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.40/0.62  fof(c_0_20, plain, ![X15, X16]:(~r1_xboole_0(X15,X16)|r1_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.40/0.62  cnf(c_0_21, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.62  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.40/0.62  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.62  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.62  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.62  fof(c_0_26, negated_conjecture, ((k4_xboole_0(esk3_0,k1_tarski(esk4_0))!=esk3_0|r2_hidden(esk4_0,esk3_0))&(k4_xboole_0(esk3_0,k1_tarski(esk4_0))=esk3_0|~r2_hidden(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.40/0.62  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.62  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.62  cnf(c_0_29, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.62  cnf(c_0_30, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.40/0.62  fof(c_0_31, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X28,X27)|(X28=X24|X28=X25|X28=X26)|X27!=k1_enumset1(X24,X25,X26))&(((X29!=X24|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))&(X29!=X25|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26)))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))))&((((esk2_4(X30,X31,X32,X33)!=X30|~r2_hidden(esk2_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32))&(esk2_4(X30,X31,X32,X33)!=X31|~r2_hidden(esk2_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(esk2_4(X30,X31,X32,X33)!=X32|~r2_hidden(esk2_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(r2_hidden(esk2_4(X30,X31,X32,X33),X33)|(esk2_4(X30,X31,X32,X33)=X30|esk2_4(X30,X31,X32,X33)=X31|esk2_4(X30,X31,X32,X33)=X32)|X33=k1_enumset1(X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.40/0.62  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|k4_xboole_0(esk3_0,k1_tarski(esk4_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.40/0.62  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.40/0.62  cnf(c_0_34, plain, (r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.40/0.62  fof(c_0_35, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.40/0.62  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.40/0.62  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk3_0,k1_tarski(esk4_0))=esk3_0|~r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.40/0.62  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_28]), c_0_24]), c_0_25])).
% 0.40/0.62  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))=X1|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.40/0.62  cnf(c_0_40, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.40/0.62  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_25])).
% 0.40/0.62  fof(c_0_42, plain, ![X17, X18, X19]:(((~r2_hidden(X17,X18)|~r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19)))&(r2_hidden(X17,X18)|r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19))))&((~r2_hidden(X17,X18)|r2_hidden(X17,X19)|r2_hidden(X17,k5_xboole_0(X18,X19)))&(~r2_hidden(X17,X19)|r2_hidden(X17,X18)|r2_hidden(X17,k5_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.40/0.62  cnf(c_0_43, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0|~r2_hidden(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_22]), c_0_23]), c_0_28]), c_0_24]), c_0_25])).
% 0.40/0.62  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.40/0.62  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.40/0.62  cnf(c_0_46, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.40/0.62  cnf(c_0_47, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.40/0.62  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.40/0.62  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.40/0.62  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_45])).
% 0.40/0.62  cnf(c_0_51, plain, (r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.40/0.62  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.40/0.62  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,X1,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_44])).
% 0.40/0.62  cnf(c_0_54, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_52, c_0_53]), ['proof']).
% 0.40/0.62  # SZS output end CNFRefutation
% 0.40/0.62  # Proof object total steps             : 55
% 0.40/0.62  # Proof object clause steps            : 30
% 0.40/0.62  # Proof object formula steps           : 25
% 0.40/0.62  # Proof object conjectures             : 12
% 0.40/0.62  # Proof object clause conjectures      : 9
% 0.40/0.62  # Proof object formula conjectures     : 3
% 0.40/0.62  # Proof object initial clauses used    : 14
% 0.40/0.62  # Proof object initial formulas used   : 12
% 0.40/0.62  # Proof object generating inferences   : 7
% 0.40/0.62  # Proof object simplifying inferences  : 24
% 0.40/0.62  # Training examples: 0 positive, 0 negative
% 0.40/0.62  # Parsed axioms                        : 12
% 0.40/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.62  # Initial clauses                      : 29
% 0.40/0.62  # Removed in clause preprocessing      : 5
% 0.40/0.62  # Initial clauses in saturation        : 24
% 0.40/0.62  # Processed clauses                    : 337
% 0.40/0.62  # ...of these trivial                  : 23
% 0.40/0.62  # ...subsumed                          : 27
% 0.40/0.62  # ...remaining for further processing  : 287
% 0.40/0.62  # Other redundant clauses eliminated   : 51
% 0.40/0.62  # Clauses deleted for lack of memory   : 0
% 0.40/0.62  # Backward-subsumed                    : 0
% 0.40/0.62  # Backward-rewritten                   : 15
% 0.40/0.62  # Generated clauses                    : 15393
% 0.40/0.62  # ...of the previous two non-trivial   : 14845
% 0.40/0.62  # Contextual simplify-reflections      : 4
% 0.40/0.62  # Paramodulations                      : 15337
% 0.40/0.62  # Factorizations                       : 8
% 0.40/0.62  # Equation resolutions                 : 51
% 0.40/0.62  # Propositional unsat checks           : 0
% 0.40/0.62  #    Propositional check models        : 0
% 0.40/0.62  #    Propositional check unsatisfiable : 0
% 0.40/0.62  #    Propositional clauses             : 0
% 0.40/0.62  #    Propositional clauses after purity: 0
% 0.40/0.62  #    Propositional unsat core size     : 0
% 0.40/0.62  #    Propositional preprocessing time  : 0.000
% 0.40/0.62  #    Propositional encoding time       : 0.000
% 0.40/0.62  #    Propositional solver time         : 0.000
% 0.40/0.62  #    Success case prop preproc time    : 0.000
% 0.40/0.62  #    Success case prop encoding time   : 0.000
% 0.40/0.62  #    Success case prop solver time     : 0.000
% 0.40/0.62  # Current number of processed clauses  : 241
% 0.40/0.62  #    Positive orientable unit clauses  : 109
% 0.40/0.62  #    Positive unorientable unit clauses: 0
% 0.40/0.62  #    Negative unit clauses             : 1
% 0.40/0.62  #    Non-unit-clauses                  : 131
% 0.40/0.62  # Current number of unprocessed clauses: 14456
% 0.40/0.62  # ...number of literals in the above   : 51285
% 0.40/0.62  # Current number of archived formulas  : 0
% 0.40/0.62  # Current number of archived clauses   : 44
% 0.40/0.62  # Clause-clause subsumption calls (NU) : 3306
% 0.40/0.62  # Rec. Clause-clause subsumption calls : 2271
% 0.40/0.62  # Non-unit clause-clause subsumptions  : 31
% 0.40/0.62  # Unit Clause-clause subsumption calls : 13
% 0.40/0.62  # Rewrite failures with RHS unbound    : 0
% 0.40/0.62  # BW rewrite match attempts            : 965
% 0.40/0.62  # BW rewrite match successes           : 2
% 0.40/0.62  # Condensation attempts                : 0
% 0.40/0.62  # Condensation successes               : 0
% 0.40/0.62  # Termbank termtop insertions          : 457027
% 0.40/0.62  
% 0.40/0.62  # -------------------------------------------------
% 0.40/0.62  # User time                : 0.252 s
% 0.40/0.62  # System time              : 0.017 s
% 0.40/0.62  # Total time               : 0.269 s
% 0.40/0.62  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
