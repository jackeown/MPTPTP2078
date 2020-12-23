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
% DateTime   : Thu Dec  3 10:59:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 162 expanded)
%              Number of clauses        :   35 (  75 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 416 expanded)
%              Number of equality atoms :  108 ( 329 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X37,X38] :
      ( k1_mcart_1(k4_tarski(X37,X38)) = X37
      & k2_mcart_1(k4_tarski(X37,X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_16,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0)
    & ( esk4_0 = k1_mcart_1(esk4_0)
      | esk4_0 = k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X39,X41,X42] :
      ( ( r2_hidden(esk3_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk3_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk3_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_24,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk2_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk2_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | esk2_3(X17,X18,X19) = X17
        | esk2_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_27,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_25])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ( k2_zfmisc_1(X31,X32) != k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk3_1(X1)) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( esk3_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X33,X34] : ~ r2_hidden(X33,k2_zfmisc_1(X33,X34)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_19]),c_0_20])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X2,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_45,negated_conjecture,
    ( k2_enumset1(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0),k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = k1_xboole_0
    | k2_mcart_1(esk4_0) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_mcart_1(esk4_0)
    | esk4_0 = k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k2_mcart_1(esk4_0) != esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk3_1(X1),X2) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( k1_mcart_1(esk4_0) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X1,X2) != X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( k4_tarski(esk4_0,k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.13/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_14, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_15, plain, ![X37, X38]:(k1_mcart_1(k4_tarski(X37,X38))=X37&k2_mcart_1(k4_tarski(X37,X38))=X38), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)&(esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_23, plain, ![X39, X41, X42]:((r2_hidden(esk3_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk3_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk3_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (esk5_0=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  fof(c_0_26, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(X15=X12|X15=X13)|X14!=k2_tarski(X12,X13))&((X16!=X12|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))))&(((esk2_3(X17,X18,X19)!=X17|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18))&(esk2_3(X17,X18,X19)!=X18|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18)))&(r2_hidden(esk2_3(X17,X18,X19),X19)|(esk2_3(X17,X18,X19)=X17|esk2_3(X17,X18,X19)=X18)|X19=k2_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk6_0)=esk4_0), inference(rw,[status(thm)],[c_0_22, c_0_25])).
% 0.13/0.38  fof(c_0_32, plain, ![X31, X32]:((k2_zfmisc_1(X31,X32)!=k1_xboole_0|(X31=k1_xboole_0|X32=k1_xboole_0))&((X31!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0)&(X32!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_34, plain, (X1=k1_xboole_0|k4_tarski(X2,esk3_1(X1))!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_35, plain, (esk3_1(k2_enumset1(X1,X1,X1,X1))=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk6_0=k2_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  fof(c_0_37, plain, ![X33, X34]:~r2_hidden(X33,k2_zfmisc_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_19]), c_0_20])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X2,X1)!=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_31, c_0_36])).
% 0.13/0.38  cnf(c_0_42, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_44, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (k2_enumset1(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0),k2_mcart_1(esk4_0),k2_mcart_1(esk4_0))=k1_xboole_0|k2_mcart_1(esk4_0)!=esk4_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_47, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k2_mcart_1(esk4_0)!=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.38  cnf(c_0_50, plain, (X1=k1_xboole_0|k4_tarski(esk3_1(X1),X2)!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_28])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k1_mcart_1(esk4_0)=esk4_0), inference(sr,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X1,X2)!=X1), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k4_tarski(esk4_0,k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_41, c_0_51])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_46]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 15
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 25
% 0.13/0.38  # Processed clauses                    : 133
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 40
% 0.13/0.38  # ...remaining for further processing  : 91
% 0.13/0.38  # Other redundant clauses eliminated   : 14
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 11
% 0.13/0.38  # Generated clauses                    : 155
% 0.13/0.38  # ...of the previous two non-trivial   : 142
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 141
% 0.13/0.38  # Factorizations                       : 2
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
% 0.13/0.38  # Current number of processed clauses  : 46
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 29
% 0.13/0.38  # Current number of unprocessed clauses: 45
% 0.13/0.38  # ...number of literals in the above   : 117
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 41
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 99
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 91
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 73
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3215
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
