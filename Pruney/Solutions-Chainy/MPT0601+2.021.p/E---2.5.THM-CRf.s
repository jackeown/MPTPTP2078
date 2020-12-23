%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 101 expanded)
%              Number of clauses        :   28 (  44 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 275 expanded)
%              Number of equality atoms :   43 (  84 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_13,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk2_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X15] : r1_xboole_0(X15,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_15,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | k11_relat_1(X22,X23) = k9_relat_1(X22,k1_tarski(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_17,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r2_hidden(k4_tarski(X37,X38),X39)
        | r2_hidden(X38,k11_relat_1(X39,X37))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X38,k11_relat_1(X39,X37))
        | r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( ~ r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(X26,esk3_3(X24,X25,X26)),X24)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X24)
        | r2_hidden(X28,X25)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(esk4_2(X30,X31),X33),X30)
        | X31 = k1_relat_1(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk4_2(X30,X31),esk5_2(X30,X31)),X30)
        | X31 = k1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
    | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X35,X36] :
      ( ( k9_relat_1(X36,X35) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X36),X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r1_xboole_0(k1_relat_1(X36),X35)
        | k9_relat_1(X36,X35) = k1_xboole_0
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_34,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk7_0)
    | ~ r2_hidden(X2,k11_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k11_relat_1(esk7_0,esk6_0)),k11_relat_1(esk7_0,esk6_0))
    | r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])]),c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) )
      & ( X19 != X21
        | ~ r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) )
      & ( ~ r2_hidden(X19,X20)
        | X19 = X21
        | r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k9_relat_1(esk7_0,k2_tarski(X1,X1)) = k11_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk7_0),k2_tarski(X1,X1))
    | k11_relat_1(esk7_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_47,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk7_0),k2_tarski(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk7_0),k2_tarski(esk6_0,esk6_0)) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.13/0.38  # and selection function SelectCQIArEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.13/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.13/0.38  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.13/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.13/0.38  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.13/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk2_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X15]:r1_xboole_0(X15,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  fof(c_0_16, plain, ![X22, X23]:(~v1_relat_1(X22)|k11_relat_1(X22,X23)=k9_relat_1(X22,k1_tarski(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_18, plain, ![X37, X38, X39]:((~r2_hidden(k4_tarski(X37,X38),X39)|r2_hidden(X38,k11_relat_1(X39,X37))|~v1_relat_1(X39))&(~r2_hidden(X38,k11_relat_1(X39,X37))|r2_hidden(k4_tarski(X37,X38),X39)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (v1_relat_1(esk7_0)&((~r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)=k1_xboole_0)&(r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_24, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(X26,esk3_3(X24,X25,X26)),X24)|X25!=k1_relat_1(X24))&(~r2_hidden(k4_tarski(X28,X29),X24)|r2_hidden(X28,X25)|X25!=k1_relat_1(X24)))&((~r2_hidden(esk4_2(X30,X31),X31)|~r2_hidden(k4_tarski(esk4_2(X30,X31),X33),X30)|X31=k1_relat_1(X30))&(r2_hidden(esk4_2(X30,X31),X31)|r2_hidden(k4_tarski(esk4_2(X30,X31),esk5_2(X30,X31)),X30)|X31=k1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_25, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_33, plain, ![X35, X36]:((k9_relat_1(X36,X35)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X36),X35)|~v1_relat_1(X36))&(~r1_xboole_0(k1_relat_1(X36),X35)|k9_relat_1(X36,X35)=k1_xboole_0|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.13/0.38  cnf(c_0_34, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk7_0)|~r2_hidden(X2,k11_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k11_relat_1(esk7_0,esk6_0)),k11_relat_1(esk7_0,esk6_0))|r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])]), c_0_31])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.38  fof(c_0_38, plain, ![X19, X20, X21]:(((r2_hidden(X19,X20)|~r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))))&(X19!=X21|~r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21)))))&(~r2_hidden(X19,X20)|X19=X21|r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k9_relat_1(esk7_0,k2_tarski(X1,X1))=k11_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  fof(c_0_44, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k1_relat_1(esk7_0),k2_tarski(X1,X1))|k11_relat_1(esk7_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.13/0.38  cnf(c_0_47, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_26])).
% 0.13/0.38  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r1_xboole_0(k1_relat_1(esk7_0),k2_tarski(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_50, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k1_relat_1(esk7_0),k2_tarski(esk6_0,esk6_0))=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_42])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 53
% 0.13/0.38  # Proof object clause steps            : 28
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 14
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 177
% 0.13/0.38  # ...of these trivial                  : 5
% 0.13/0.38  # ...subsumed                          : 71
% 0.13/0.38  # ...remaining for further processing  : 101
% 0.13/0.38  # Other redundant clauses eliminated   : 14
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 715
% 0.13/0.38  # ...of the previous two non-trivial   : 640
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 701
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 14
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 71
% 0.13/0.38  #    Positive orientable unit clauses  : 12
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 56
% 0.13/0.38  # Current number of unprocessed clauses: 507
% 0.13/0.38  # ...number of literals in the above   : 1619
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 28
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 878
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 766
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 57
% 0.13/0.38  # Unit Clause-clause subsumption calls : 4
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 10033
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
