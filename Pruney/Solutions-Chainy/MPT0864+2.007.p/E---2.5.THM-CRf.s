%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 140 expanded)
%              Number of clauses        :   31 (  65 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 340 expanded)
%              Number of equality atoms :   84 ( 267 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(c_0_8,plain,(
    ! [X41,X42] : k2_xboole_0(k1_tarski(X41),X42) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X10
        | X13 = X11
        | X12 != k2_tarski(X10,X11) )
      & ( X14 != X10
        | r2_hidden(X14,X12)
        | X12 != k2_tarski(X10,X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k2_tarski(X10,X11) )
      & ( esk1_3(X15,X16,X17) != X15
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_tarski(X15,X16) )
      & ( esk1_3(X15,X16,X17) != X16
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_tarski(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | esk1_3(X15,X16,X17) = X15
        | esk1_3(X15,X16,X17) = X16
        | X17 = k2_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_13,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_17,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_18,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0)
    & ( esk8_0 = k1_mcart_1(esk8_0)
      | esk8_0 = k2_mcart_1(esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X50,X52,X53] :
      ( ( r2_hidden(esk7_1(X50),X50)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X52,X50)
        | esk7_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X50)
        | esk7_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_23,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 = k1_mcart_1(esk8_0)
    | esk8_0 = k2_mcart_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k1_mcart_1(esk8_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk7_1(k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk7_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( esk7_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk10_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(esk9_0,esk8_0) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_43,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk7_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( esk9_0 = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_26])])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(esk8_0,esk10_0) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.14/0.38  # and selection function SelectNegativeLiterals.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.14/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.14/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.14/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.14/0.38  fof(c_0_8, plain, ![X41, X42]:k2_xboole_0(k1_tarski(X41),X42)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_10, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.14/0.38  fof(c_0_12, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(X13=X10|X13=X11)|X12!=k2_tarski(X10,X11))&((X14!=X10|r2_hidden(X14,X12)|X12!=k2_tarski(X10,X11))&(X14!=X11|r2_hidden(X14,X12)|X12!=k2_tarski(X10,X11))))&(((esk1_3(X15,X16,X17)!=X15|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_tarski(X15,X16))&(esk1_3(X15,X16,X17)!=X16|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_tarski(X15,X16)))&(r2_hidden(esk1_3(X15,X16,X17),X17)|(esk1_3(X15,X16,X17)=X15|esk1_3(X15,X16,X17)=X16)|X17=k2_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_13, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_16, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.14/0.38  fof(c_0_17, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.14/0.38  fof(c_0_18, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)&(esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.14/0.38  cnf(c_0_19, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_20, plain, (k2_xboole_0(k1_enumset1(X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.14/0.38  cnf(c_0_21, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  fof(c_0_22, plain, ![X50, X52, X53]:((r2_hidden(esk7_1(X50),X50)|X50=k1_xboole_0)&((~r2_hidden(X52,X50)|esk7_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0)&(~r2_hidden(X53,X50)|esk7_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.14/0.38  cnf(c_0_23, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.14/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(esk7_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_28, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (k1_mcart_1(esk8_0)=esk9_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_31, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_32, plain, (r2_hidden(esk7_1(k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k2_mcart_1(esk8_0)=esk10_0), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (k2_mcart_1(esk8_0)=esk8_0|esk9_0=esk8_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_36, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk7_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_37, plain, (esk7_1(k1_enumset1(X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (esk9_0=esk8_0|esk10_0=esk8_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_35, c_0_15])).
% 0.14/0.38  cnf(c_0_40, plain, (~r2_hidden(X1,k1_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_26])])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (k4_tarski(esk9_0,esk8_0)=esk8_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_24, c_0_38])).
% 0.14/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.14/0.38  cnf(c_0_43, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk7_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (esk9_0=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.14/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_26])])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (k4_tarski(esk8_0,esk10_0)=esk8_0), inference(rw,[status(thm)],[c_0_24, c_0_44])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 48
% 0.14/0.38  # Proof object clause steps            : 31
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 11
% 0.14/0.38  # Proof object simplifying inferences  : 17
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 13
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 34
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 32
% 0.14/0.38  # Processed clauses                    : 97
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 8
% 0.14/0.38  # ...remaining for further processing  : 89
% 0.14/0.38  # Other redundant clauses eliminated   : 18
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 10
% 0.14/0.38  # Generated clauses                    : 131
% 0.14/0.38  # ...of the previous two non-trivial   : 113
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 116
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 18
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
% 0.14/0.38  # Current number of processed clauses  : 35
% 0.14/0.38  #    Positive orientable unit clauses  : 13
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 6
% 0.14/0.38  #    Non-unit-clauses                  : 16
% 0.14/0.38  # Current number of unprocessed clauses: 72
% 0.14/0.38  # ...number of literals in the above   : 185
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 45
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 136
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 94
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.14/0.38  # Unit Clause-clause subsumption calls : 28
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 9
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3115
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
