%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 104 expanded)
%              Number of clauses        :   34 (  50 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 271 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t87_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_12,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X17,X16)
        | r2_hidden(X17,X15)
        | ~ r1_xboole_0(X15,X16)
        | ~ r2_hidden(X17,k2_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X17,X15)
        | r2_hidden(X17,X15)
        | ~ r1_xboole_0(X15,X16)
        | ~ r2_hidden(X17,k2_xboole_0(X15,X16)) )
      & ( r2_hidden(X17,X16)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16)
        | ~ r2_hidden(X17,k2_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16)
        | ~ r2_hidden(X17,k2_xboole_0(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

cnf(c_0_22,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_25,plain,(
    ! [X27,X28,X29] :
      ( r1_xboole_0(X27,X28)
      | ~ r1_tarski(X27,X29)
      | ~ r1_xboole_0(X27,k3_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

fof(c_0_26,plain,(
    ! [X32,X33] :
      ( ( ~ r1_xboole_0(X32,X33)
        | k4_xboole_0(X32,X33) = X32 )
      & ( k4_xboole_0(X32,X33) != X32
        | r1_xboole_0(X32,X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] : k4_xboole_0(X23,k4_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X23,X24),k3_xboole_0(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t87_xboole_1])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_17,c_0_28])).

fof(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    & k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk4_0) != k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k3_xboole_0(X2,X3)) != X1
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) != X1
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X26] : r1_xboole_0(X26,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) != X1
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0)
    | k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk3_0)) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

fof(c_0_52,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk4_0) != k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0) = k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.028 s
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.52  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.52  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 0.20/0.52  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.20/0.52  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.20/0.52  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.52  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.20/0.52  fof(t87_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 0.20/0.52  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.52  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.52  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.52  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.52  fof(c_0_12, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.52  fof(c_0_13, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.52  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.52  cnf(c_0_15, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.52  fof(c_0_16, plain, ![X15, X16, X17]:(((r2_hidden(X17,X16)|(r2_hidden(X17,X15)|(~r1_xboole_0(X15,X16)|~r2_hidden(X17,k2_xboole_0(X15,X16)))))&(~r2_hidden(X17,X15)|(r2_hidden(X17,X15)|(~r1_xboole_0(X15,X16)|~r2_hidden(X17,k2_xboole_0(X15,X16))))))&((r2_hidden(X17,X16)|(~r2_hidden(X17,X16)|(~r1_xboole_0(X15,X16)|~r2_hidden(X17,k2_xboole_0(X15,X16)))))&(~r2_hidden(X17,X15)|(~r2_hidden(X17,X16)|(~r1_xboole_0(X15,X16)|~r2_hidden(X17,k2_xboole_0(X15,X16))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 0.20/0.52  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.52  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.52  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.52  cnf(c_0_20, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.52  fof(c_0_21, plain, ![X30, X31]:r1_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.20/0.52  cnf(c_0_22, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.52  cnf(c_0_23, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.52  cnf(c_0_24, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.52  fof(c_0_25, plain, ![X27, X28, X29]:(r1_xboole_0(X27,X28)|~r1_tarski(X27,X29)|~r1_xboole_0(X27,k3_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.20/0.52  fof(c_0_26, plain, ![X32, X33]:((~r1_xboole_0(X32,X33)|k4_xboole_0(X32,X33)=X32)&(k4_xboole_0(X32,X33)!=X32|r1_xboole_0(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.52  fof(c_0_27, plain, ![X23, X24, X25]:k4_xboole_0(X23,k4_xboole_0(X24,X25))=k2_xboole_0(k4_xboole_0(X23,X24),k3_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.20/0.52  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_15])).
% 0.20/0.52  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1))), inference(assume_negation,[status(cth)],[t87_xboole_1])).
% 0.20/0.52  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.52  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.52  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_33, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_17, c_0_28])).
% 0.20/0.52  fof(c_0_34, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)&k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk4_0)!=k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.20/0.52  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k3_xboole_0(X2,X3))!=X1|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.52  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.52  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.52  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.52  fof(c_0_39, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.52  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))!=X1|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.52  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.52  fof(c_0_42, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.52  cnf(c_0_43, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.52  fof(c_0_44, plain, ![X26]:r1_xboole_0(X26,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.52  cnf(c_0_45, negated_conjecture, (r1_xboole_0(X1,esk3_0)|k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))!=X1|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.52  cnf(c_0_46, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.52  cnf(c_0_47, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.20/0.52  cnf(c_0_48, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.52  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)|k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk3_0))!=esk4_0), inference(spm,[status(thm)],[c_0_45, c_0_18])).
% 0.20/0.52  cnf(c_0_50, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.52  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 0.20/0.52  fof(c_0_52, plain, ![X20, X21, X22]:k4_xboole_0(k2_xboole_0(X20,X21),X22)=k2_xboole_0(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.52  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.20/0.52  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.52  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_37, c_0_53])).
% 0.20/0.52  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk4_0)!=k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.52  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)=k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.52  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 59
% 0.20/0.52  # Proof object clause steps            : 34
% 0.20/0.52  # Proof object formula steps           : 25
% 0.20/0.52  # Proof object conjectures             : 12
% 0.20/0.52  # Proof object clause conjectures      : 9
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 15
% 0.20/0.52  # Proof object initial formulas used   : 12
% 0.20/0.52  # Proof object generating inferences   : 17
% 0.20/0.52  # Proof object simplifying inferences  : 5
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 13
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 21
% 0.20/0.52  # Removed in clause preprocessing      : 2
% 0.20/0.52  # Initial clauses in saturation        : 19
% 0.20/0.52  # Processed clauses                    : 954
% 0.20/0.52  # ...of these trivial                  : 49
% 0.20/0.52  # ...subsumed                          : 608
% 0.20/0.52  # ...remaining for further processing  : 297
% 0.20/0.52  # Other redundant clauses eliminated   : 2
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 4
% 0.20/0.52  # Backward-rewritten                   : 35
% 0.20/0.52  # Generated clauses                    : 11415
% 0.20/0.52  # ...of the previous two non-trivial   : 9520
% 0.20/0.52  # Contextual simplify-reflections      : 2
% 0.20/0.52  # Paramodulations                      : 11409
% 0.20/0.52  # Factorizations                       : 4
% 0.20/0.52  # Equation resolutions                 : 2
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 258
% 0.20/0.52  #    Positive orientable unit clauses  : 80
% 0.20/0.52  #    Positive unorientable unit clauses: 3
% 0.20/0.52  #    Negative unit clauses             : 4
% 0.20/0.52  #    Non-unit-clauses                  : 171
% 0.20/0.52  # Current number of unprocessed clauses: 8408
% 0.20/0.52  # ...number of literals in the above   : 23193
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 39
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 6507
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 4482
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 381
% 0.20/0.52  # Unit Clause-clause subsumption calls : 166
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 136
% 0.20/0.52  # BW rewrite match successes           : 18
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 167837
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.158 s
% 0.20/0.52  # System time              : 0.013 s
% 0.20/0.52  # Total time               : 0.171 s
% 0.20/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
