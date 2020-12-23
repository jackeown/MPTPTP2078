%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (1685 expanded)
%              Number of clauses        :   35 ( 684 expanded)
%              Number of leaves         :    9 ( 480 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 (2851 expanded)
%              Number of equality atoms :   76 (2473 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X8,X9] : r1_tarski(X8,k2_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_13,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_xboole_0(esk2_0,esk3_0)
    & ( esk2_0 != k1_tarski(esk1_0)
      | esk3_0 != k1_tarski(esk1_0) )
    & ( esk2_0 != k1_xboole_0
      | esk3_0 != k1_tarski(esk1_0) )
    & ( esk2_0 != k1_tarski(esk1_0)
      | esk3_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ( ~ r1_tarski(X18,k1_tarski(X19))
        | X18 = k1_xboole_0
        | X18 = k1_tarski(X19) )
      & ( X18 != k1_xboole_0
        | r1_tarski(X18,k1_tarski(X19)) )
      & ( X18 != k1_tarski(X19)
        | r1_tarski(X18,k1_tarski(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_22,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) = k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_19]),c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 != k1_tarski(esk1_0)
    | esk3_0 != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)
    | esk3_0 != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 != k1_tarski(esk1_0)
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X1 = esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | esk3_0 != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | esk3_0 != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k1_xboole_0)) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_48]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_28]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.36  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.13/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.13/0.36  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.13/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.13/0.36  fof(c_0_10, plain, ![X8, X9]:r1_tarski(X8,k2_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.36  fof(c_0_11, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.36  fof(c_0_12, plain, ![X7]:k2_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.36  fof(c_0_13, negated_conjecture, (((k1_tarski(esk1_0)=k2_xboole_0(esk2_0,esk3_0)&(esk2_0!=k1_tarski(esk1_0)|esk3_0!=k1_tarski(esk1_0)))&(esk2_0!=k1_xboole_0|esk3_0!=k1_tarski(esk1_0)))&(esk2_0!=k1_tarski(esk1_0)|esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.36  fof(c_0_14, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_15, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_16, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_17, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.13/0.36  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_20, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  fof(c_0_21, plain, ![X18, X19]:((~r1_tarski(X18,k1_tarski(X19))|(X18=k1_xboole_0|X18=k1_tarski(X19)))&((X18!=k1_xboole_0|r1_tarski(X18,k1_tarski(X19)))&(X18!=k1_tarski(X19)|r1_tarski(X18,k1_tarski(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (k1_tarski(esk1_0)=k2_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.36  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_27, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.36  cnf(c_0_28, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.13/0.36  cnf(c_0_29, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_30, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)=k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_19]), c_0_25])).
% 0.13/0.36  cnf(c_0_31, plain, (r1_tarski(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.13/0.36  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.36  cnf(c_0_33, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.13/0.36  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.13/0.36  cnf(c_0_35, plain, (r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (esk2_0!=k1_tarski(esk1_0)|esk3_0!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (esk2_0!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)|esk3_0!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (esk2_0!=k1_tarski(esk1_0)|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|X1=k1_xboole_0|X1=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (esk2_0!=k1_xboole_0|esk3_0!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.36  cnf(c_0_47, negated_conjecture, (esk2_0!=k1_xboole_0|esk3_0!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37])).
% 0.13/0.36  cnf(c_0_49, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.13/0.36  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_49])).
% 0.13/0.36  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k1_xboole_0))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_48]), c_0_48])).
% 0.13/0.36  cnf(c_0_52, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.36  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_28]), c_0_52]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 54
% 0.13/0.36  # Proof object clause steps            : 35
% 0.13/0.36  # Proof object formula steps           : 19
% 0.13/0.36  # Proof object conjectures             : 24
% 0.13/0.36  # Proof object clause conjectures      : 21
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 12
% 0.13/0.36  # Proof object initial formulas used   : 9
% 0.13/0.36  # Proof object generating inferences   : 11
% 0.13/0.36  # Proof object simplifying inferences  : 36
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 9
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 14
% 0.13/0.36  # Removed in clause preprocessing      : 4
% 0.13/0.36  # Initial clauses in saturation        : 10
% 0.13/0.36  # Processed clauses                    : 43
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 2
% 0.13/0.36  # ...remaining for further processing  : 40
% 0.13/0.36  # Other redundant clauses eliminated   : 2
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 18
% 0.13/0.36  # Generated clauses                    : 33
% 0.13/0.36  # ...of the previous two non-trivial   : 33
% 0.13/0.36  # Contextual simplify-reflections      : 2
% 0.13/0.36  # Paramodulations                      : 31
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 2
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 10
% 0.13/0.36  #    Positive orientable unit clauses  : 7
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 2
% 0.13/0.36  # Current number of unprocessed clauses: 10
% 0.13/0.36  # ...number of literals in the above   : 14
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 32
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 9
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.36  # Unit Clause-clause subsumption calls : 4
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 14
% 0.13/0.36  # BW rewrite match successes           : 6
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1058
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.028 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.031 s
% 0.13/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
