%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:18 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   56 (  98 expanded)
%              Number of clauses        :   35 (  49 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 311 expanded)
%              Number of equality atoms :   77 ( 136 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t31_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X47,X48] :
      ( ( k4_xboole_0(k1_tarski(X47),k1_tarski(X48)) != k1_tarski(X47)
        | X47 != X48 )
      & ( X47 = X48
        | k4_xboole_0(k1_tarski(X47),k1_tarski(X48)) = k1_tarski(X47) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X24
        | X27 = X25
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( esk3_3(X29,X30,X31) != X29
        | ~ r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( esk3_3(X29,X30,X31) != X30
        | ~ r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( r2_hidden(esk3_3(X29,X30,X31),X31)
        | esk3_3(X29,X30,X31) = X29
        | esk3_3(X29,X30,X31) = X30
        | X31 = k2_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 = X2
    | k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k2_tarski(X1,X1))
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( r2_hidden(X38,esk4_3(X36,X37,X38))
        | ~ r2_hidden(X38,X37)
        | X37 != k3_tarski(X36) )
      & ( r2_hidden(esk4_3(X36,X37,X38),X36)
        | ~ r2_hidden(X38,X37)
        | X37 != k3_tarski(X36) )
      & ( ~ r2_hidden(X40,X41)
        | ~ r2_hidden(X41,X36)
        | r2_hidden(X40,X37)
        | X37 != k3_tarski(X36) )
      & ( ~ r2_hidden(esk5_2(X42,X43),X43)
        | ~ r2_hidden(esk5_2(X42,X43),X45)
        | ~ r2_hidden(X45,X42)
        | X43 = k3_tarski(X42) )
      & ( r2_hidden(esk5_2(X42,X43),esk6_2(X42,X43))
        | r2_hidden(esk5_2(X42,X43),X43)
        | X43 = k3_tarski(X42) )
      & ( r2_hidden(esk6_2(X42,X43),X42)
        | r2_hidden(esk5_2(X42,X43),X43)
        | X43 = k3_tarski(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X33,X34] : k2_tarski(X33,X34) = k2_xboole_0(k1_tarski(X33),k1_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( esk4_3(k2_tarski(X1,X1),X2,X3) = X1
    | X2 != k3_tarski(k2_tarski(X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_tarski(k2_tarski(X3,X4))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

fof(c_0_32,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X3 != k3_tarski(k2_tarski(X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_16]),c_0_16])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t31_zfmisc_1])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(k2_tarski(X2,X2))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(esk1_2(X1,k3_tarski(k2_tarski(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,negated_conjecture,(
    k3_tarski(k1_tarski(esk7_0)) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_45,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(k3_tarski(k2_tarski(X1,X1)),X2),X1)
    | r1_tarski(k3_tarski(k2_tarski(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(k1_tarski(esk7_0)) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_16])).

cnf(c_0_54,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.09/1.26  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.09/1.26  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.09/1.26  #
% 1.09/1.26  # Preprocessing time       : 0.028 s
% 1.09/1.26  # Presaturation interreduction done
% 1.09/1.26  
% 1.09/1.26  # Proof found!
% 1.09/1.26  # SZS status Theorem
% 1.09/1.26  # SZS output start CNFRefutation
% 1.09/1.26  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.09/1.26  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.09/1.26  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.09/1.26  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.09/1.26  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.09/1.26  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.09/1.26  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.09/1.26  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.09/1.26  fof(t31_zfmisc_1, conjecture, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.09/1.26  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.09/1.26  fof(c_0_10, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.09/1.26  fof(c_0_11, plain, ![X47, X48]:((k4_xboole_0(k1_tarski(X47),k1_tarski(X48))!=k1_tarski(X47)|X47!=X48)&(X47=X48|k4_xboole_0(k1_tarski(X47),k1_tarski(X48))=k1_tarski(X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 1.09/1.26  fof(c_0_12, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.09/1.26  fof(c_0_13, plain, ![X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X27,X26)|(X27=X24|X27=X25)|X26!=k2_tarski(X24,X25))&((X28!=X24|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))))&(((esk3_3(X29,X30,X31)!=X29|~r2_hidden(esk3_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30))&(esk3_3(X29,X30,X31)!=X30|~r2_hidden(esk3_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30)))&(r2_hidden(esk3_3(X29,X30,X31),X31)|(esk3_3(X29,X30,X31)=X29|esk3_3(X29,X30,X31)=X30)|X31=k2_tarski(X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 1.09/1.26  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.09/1.26  cnf(c_0_15, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.09/1.26  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.09/1.26  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.09/1.26  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 1.09/1.26  cnf(c_0_19, plain, (X1=X2|k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_16])).
% 1.09/1.26  cnf(c_0_20, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X3,X1)), inference(er,[status(thm)],[c_0_17])).
% 1.09/1.26  cnf(c_0_21, plain, (X1=X2|~r2_hidden(X3,k2_tarski(X1,X1))|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.09/1.26  cnf(c_0_22, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[c_0_20])).
% 1.09/1.26  fof(c_0_23, plain, ![X36, X37, X38, X40, X41, X42, X43, X45]:((((r2_hidden(X38,esk4_3(X36,X37,X38))|~r2_hidden(X38,X37)|X37!=k3_tarski(X36))&(r2_hidden(esk4_3(X36,X37,X38),X36)|~r2_hidden(X38,X37)|X37!=k3_tarski(X36)))&(~r2_hidden(X40,X41)|~r2_hidden(X41,X36)|r2_hidden(X40,X37)|X37!=k3_tarski(X36)))&((~r2_hidden(esk5_2(X42,X43),X43)|(~r2_hidden(esk5_2(X42,X43),X45)|~r2_hidden(X45,X42))|X43=k3_tarski(X42))&((r2_hidden(esk5_2(X42,X43),esk6_2(X42,X43))|r2_hidden(esk5_2(X42,X43),X43)|X43=k3_tarski(X42))&(r2_hidden(esk6_2(X42,X43),X42)|r2_hidden(esk5_2(X42,X43),X43)|X43=k3_tarski(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.09/1.26  cnf(c_0_24, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.09/1.26  cnf(c_0_25, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.09/1.26  cnf(c_0_26, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.09/1.26  fof(c_0_27, plain, ![X33, X34]:k2_tarski(X33,X34)=k2_xboole_0(k1_tarski(X33),k1_tarski(X34)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 1.09/1.26  cnf(c_0_28, plain, (r2_hidden(X1,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.09/1.26  cnf(c_0_29, plain, (esk4_3(k2_tarski(X1,X1),X2,X3)=X1|X2!=k3_tarski(k2_tarski(X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.09/1.26  fof(c_0_30, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.09/1.26  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X2!=k3_tarski(k2_tarski(X3,X4))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 1.09/1.26  fof(c_0_32, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.09/1.26  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.09/1.26  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X3!=k3_tarski(k2_tarski(X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.09/1.26  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.09/1.26  cnf(c_0_36, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 1.09/1.26  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.09/1.26  cnf(c_0_38, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_16]), c_0_16])).
% 1.09/1.26  fof(c_0_39, negated_conjecture, ~(![X1]:k3_tarski(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t31_zfmisc_1])).
% 1.09/1.26  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_tarski(k2_tarski(X2,X2)))), inference(er,[status(thm)],[c_0_34])).
% 1.09/1.26  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.09/1.26  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(esk1_2(X1,k3_tarski(k2_tarski(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.09/1.26  cnf(c_0_43, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.09/1.26  fof(c_0_44, negated_conjecture, k3_tarski(k1_tarski(esk7_0))!=esk7_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 1.09/1.26  fof(c_0_45, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.09/1.26  cnf(c_0_46, plain, (r2_hidden(esk1_2(k3_tarski(k2_tarski(X1,X1)),X2),X1)|r1_tarski(k3_tarski(k2_tarski(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.09/1.26  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 1.09/1.26  cnf(c_0_48, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 1.09/1.26  cnf(c_0_49, negated_conjecture, (k3_tarski(k1_tarski(esk7_0))!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.09/1.26  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.09/1.26  cnf(c_0_51, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 1.09/1.26  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.09/1.26  cnf(c_0_53, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))!=esk7_0), inference(rw,[status(thm)],[c_0_49, c_0_16])).
% 1.09/1.26  cnf(c_0_54, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 1.09/1.26  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])]), ['proof']).
% 1.09/1.26  # SZS output end CNFRefutation
% 1.09/1.26  # Proof object total steps             : 56
% 1.09/1.26  # Proof object clause steps            : 35
% 1.09/1.26  # Proof object formula steps           : 21
% 1.09/1.26  # Proof object conjectures             : 6
% 1.09/1.26  # Proof object clause conjectures      : 3
% 1.09/1.26  # Proof object formula conjectures     : 3
% 1.09/1.26  # Proof object initial clauses used    : 13
% 1.09/1.26  # Proof object initial formulas used   : 10
% 1.09/1.26  # Proof object generating inferences   : 17
% 1.09/1.26  # Proof object simplifying inferences  : 11
% 1.09/1.26  # Training examples: 0 positive, 0 negative
% 1.09/1.26  # Parsed axioms                        : 10
% 1.09/1.26  # Removed by relevancy pruning/SinE    : 0
% 1.09/1.26  # Initial clauses                      : 30
% 1.09/1.26  # Removed in clause preprocessing      : 1
% 1.09/1.26  # Initial clauses in saturation        : 29
% 1.09/1.26  # Processed clauses                    : 11020
% 1.09/1.26  # ...of these trivial                  : 531
% 1.09/1.26  # ...subsumed                          : 9004
% 1.09/1.26  # ...remaining for further processing  : 1485
% 1.09/1.26  # Other redundant clauses eliminated   : 135
% 1.09/1.26  # Clauses deleted for lack of memory   : 0
% 1.09/1.26  # Backward-subsumed                    : 26
% 1.09/1.26  # Backward-rewritten                   : 56
% 1.09/1.26  # Generated clauses                    : 89414
% 1.09/1.26  # ...of the previous two non-trivial   : 83040
% 1.09/1.26  # Contextual simplify-reflections      : 2
% 1.09/1.26  # Paramodulations                      : 88997
% 1.09/1.26  # Factorizations                       : 68
% 1.09/1.26  # Equation resolutions                 : 349
% 1.09/1.26  # Propositional unsat checks           : 0
% 1.09/1.26  #    Propositional check models        : 0
% 1.09/1.26  #    Propositional check unsatisfiable : 0
% 1.09/1.26  #    Propositional clauses             : 0
% 1.09/1.26  #    Propositional clauses after purity: 0
% 1.09/1.26  #    Propositional unsat core size     : 0
% 1.09/1.26  #    Propositional preprocessing time  : 0.000
% 1.09/1.26  #    Propositional encoding time       : 0.000
% 1.09/1.26  #    Propositional solver time         : 0.000
% 1.09/1.26  #    Success case prop preproc time    : 0.000
% 1.09/1.26  #    Success case prop encoding time   : 0.000
% 1.09/1.26  #    Success case prop solver time     : 0.000
% 1.09/1.26  # Current number of processed clauses  : 1370
% 1.09/1.26  #    Positive orientable unit clauses  : 331
% 1.09/1.26  #    Positive unorientable unit clauses: 26
% 1.09/1.26  #    Negative unit clauses             : 148
% 1.09/1.26  #    Non-unit-clauses                  : 865
% 1.09/1.26  # Current number of unprocessed clauses: 71994
% 1.09/1.26  # ...number of literals in the above   : 171412
% 1.09/1.26  # Current number of archived formulas  : 0
% 1.09/1.26  # Current number of archived clauses   : 111
% 1.09/1.26  # Clause-clause subsumption calls (NU) : 143090
% 1.09/1.26  # Rec. Clause-clause subsumption calls : 88934
% 1.09/1.26  # Non-unit clause-clause subsumptions  : 3161
% 1.09/1.26  # Unit Clause-clause subsumption calls : 42448
% 1.09/1.26  # Rewrite failures with RHS unbound    : 661
% 1.09/1.26  # BW rewrite match attempts            : 21937
% 1.09/1.26  # BW rewrite match successes           : 175
% 1.09/1.26  # Condensation attempts                : 0
% 1.09/1.26  # Condensation successes               : 0
% 1.09/1.26  # Termbank termtop insertions          : 1648652
% 1.09/1.27  
% 1.09/1.27  # -------------------------------------------------
% 1.09/1.27  # User time                : 0.873 s
% 1.09/1.27  # System time              : 0.050 s
% 1.09/1.27  # Total time               : 0.923 s
% 1.09/1.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
