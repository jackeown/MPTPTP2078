%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 161 expanded)
%              Number of clauses        :   30 (  63 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 203 expanded)
%              Number of equality atoms :   59 ( 164 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(l20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_14,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_15,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X42),X43),X43)
      | r2_hidden(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

fof(c_0_33,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X25
        | X26 != k1_tarski(X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k1_tarski(X25) )
      & ( ~ r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) != X29
        | X30 = k1_tarski(X29) )
      & ( r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) = X29
        | X30 = k1_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_20]),c_0_21]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_46,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_35]),c_0_36]),c_0_20]),c_0_21]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_20]),c_0_21])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_52,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:58:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.029 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.39  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.18/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.39  fof(l20_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 0.18/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.39  fof(c_0_14, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.39  fof(c_0_15, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.39  fof(c_0_16, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.39  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.39  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.18/0.39  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.39  fof(c_0_23, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.18/0.39  fof(c_0_24, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.39  fof(c_0_25, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.39  fof(c_0_26, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  fof(c_0_27, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.39  fof(c_0_28, plain, ![X42, X43]:(~r1_tarski(k2_xboole_0(k1_tarski(X42),X43),X43)|r2_hidden(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).
% 0.18/0.39  fof(c_0_29, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.39  fof(c_0_30, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.39  cnf(c_0_31, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.18/0.39  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.18/0.39  fof(c_0_33, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  fof(c_0_39, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|X27=X25|X26!=k1_tarski(X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k1_tarski(X25)))&((~r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)!=X29|X30=k1_tarski(X29))&(r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)=X29|X30=k1_tarski(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.39  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.39  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  cnf(c_0_43, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.39  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_20]), c_0_21]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.18/0.39  cnf(c_0_46, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.39  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_35]), c_0_36]), c_0_20]), c_0_21]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.18/0.39  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_20]), c_0_21])).
% 0.18/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.18/0.39  cnf(c_0_50, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 0.18/0.39  cnf(c_0_52, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.18/0.39  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.39  cnf(c_0_55, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 59
% 0.18/0.39  # Proof object clause steps            : 30
% 0.18/0.39  # Proof object formula steps           : 29
% 0.18/0.39  # Proof object conjectures             : 10
% 0.18/0.39  # Proof object clause conjectures      : 7
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 15
% 0.18/0.39  # Proof object initial formulas used   : 14
% 0.18/0.39  # Proof object generating inferences   : 6
% 0.18/0.39  # Proof object simplifying inferences  : 44
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 18
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 24
% 0.18/0.39  # Removed in clause preprocessing      : 6
% 0.18/0.39  # Initial clauses in saturation        : 18
% 0.18/0.39  # Processed clauses                    : 366
% 0.18/0.39  # ...of these trivial                  : 18
% 0.18/0.39  # ...subsumed                          : 225
% 0.18/0.39  # ...remaining for further processing  : 123
% 0.18/0.39  # Other redundant clauses eliminated   : 6
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 4
% 0.18/0.39  # Backward-rewritten                   : 29
% 0.18/0.39  # Generated clauses                    : 1489
% 0.18/0.39  # ...of the previous two non-trivial   : 1078
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 1484
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 6
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 69
% 0.18/0.39  #    Positive orientable unit clauses  : 19
% 0.18/0.39  #    Positive unorientable unit clauses: 2
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 47
% 0.18/0.39  # Current number of unprocessed clauses: 735
% 0.18/0.39  # ...number of literals in the above   : 2630
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 56
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 1585
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 1504
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 222
% 0.18/0.39  # Unit Clause-clause subsumption calls : 9
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 106
% 0.18/0.39  # BW rewrite match successes           : 23
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 26944
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.055 s
% 0.18/0.39  # System time              : 0.006 s
% 0.18/0.39  # Total time               : 0.061 s
% 0.18/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
