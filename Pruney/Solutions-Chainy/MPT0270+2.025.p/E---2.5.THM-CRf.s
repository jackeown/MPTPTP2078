%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:39 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 268 expanded)
%              Number of clauses        :   35 ( 113 expanded)
%              Number of leaves         :    8 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 642 expanded)
%              Number of equality atoms :   84 ( 420 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
      <=> ~ r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t67_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_tarski(esk5_0)
      | r2_hidden(esk5_0,esk6_0) )
    & ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_tarski(esk5_0)
      | ~ r2_hidden(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X34,X35] : k4_xboole_0(X34,X35) = k5_xboole_0(X34,k3_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X55,X56,X57] : k2_enumset1(X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X26,X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(X27,X23)
        | r2_hidden(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk3_3(X28,X29,X30),X30)
        | ~ r2_hidden(esk3_3(X28,X29,X30),X28)
        | r2_hidden(esk3_3(X28,X29,X30),X29)
        | X30 = k4_xboole_0(X28,X29) )
      & ( r2_hidden(esk3_3(X28,X29,X30),X28)
        | r2_hidden(esk3_3(X28,X29,X30),X30)
        | X30 = k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(esk3_3(X28,X29,X30),X29)
        | r2_hidden(esk3_3(X28,X29,X30),X30)
        | X30 = k4_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_15,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X45,X44)
        | X45 = X41
        | X45 = X42
        | X45 = X43
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X41
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X42
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X43
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( esk4_4(X47,X48,X49,X50) != X47
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( esk4_4(X47,X48,X49,X50) != X48
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( esk4_4(X47,X48,X49,X50) != X49
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | esk4_4(X47,X48,X49,X50) = X47
        | esk4_4(X47,X48,X49,X50) = X48
        | esk4_4(X47,X48,X49,X50) = X49
        | X50 = k1_enumset1(X47,X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | r2_hidden(esk3_3(X2,X3,X1),X2)
    | r2_hidden(esk3_3(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_tarski(esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_3(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( esk3_3(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25]),c_0_42])]),c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.15/1.33  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.15/1.33  # and selection function SelectNegativeLiterals.
% 1.15/1.33  #
% 1.15/1.33  # Preprocessing time       : 0.030 s
% 1.15/1.33  # Presaturation interreduction done
% 1.15/1.33  
% 1.15/1.33  # Proof found!
% 1.15/1.33  # SZS status Theorem
% 1.15/1.33  # SZS output start CNFRefutation
% 1.15/1.33  fof(t67_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 1.15/1.33  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.15/1.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.15/1.33  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.15/1.33  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.15/1.33  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.15/1.33  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.15/1.33  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.15/1.33  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2)))), inference(assume_negation,[status(cth)],[t67_zfmisc_1])).
% 1.15/1.33  fof(c_0_9, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk5_0)|r2_hidden(esk5_0,esk6_0))&(k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_tarski(esk5_0)|~r2_hidden(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 1.15/1.33  fof(c_0_10, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.15/1.33  fof(c_0_11, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.15/1.33  fof(c_0_12, plain, ![X34, X35]:k4_xboole_0(X34,X35)=k5_xboole_0(X34,k3_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.15/1.33  fof(c_0_13, plain, ![X55, X56, X57]:k2_enumset1(X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.15/1.33  fof(c_0_14, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:((((r2_hidden(X26,X23)|~r2_hidden(X26,X25)|X25!=k4_xboole_0(X23,X24))&(~r2_hidden(X26,X24)|~r2_hidden(X26,X25)|X25!=k4_xboole_0(X23,X24)))&(~r2_hidden(X27,X23)|r2_hidden(X27,X24)|r2_hidden(X27,X25)|X25!=k4_xboole_0(X23,X24)))&((~r2_hidden(esk3_3(X28,X29,X30),X30)|(~r2_hidden(esk3_3(X28,X29,X30),X28)|r2_hidden(esk3_3(X28,X29,X30),X29))|X30=k4_xboole_0(X28,X29))&((r2_hidden(esk3_3(X28,X29,X30),X28)|r2_hidden(esk3_3(X28,X29,X30),X30)|X30=k4_xboole_0(X28,X29))&(~r2_hidden(esk3_3(X28,X29,X30),X29)|r2_hidden(esk3_3(X28,X29,X30),X30)|X30=k4_xboole_0(X28,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.15/1.33  fof(c_0_15, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X45,X44)|(X45=X41|X45=X42|X45=X43)|X44!=k1_enumset1(X41,X42,X43))&(((X46!=X41|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43))&(X46!=X42|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43)))&(X46!=X43|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43))))&((((esk4_4(X47,X48,X49,X50)!=X47|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49))&(esk4_4(X47,X48,X49,X50)!=X48|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49)))&(esk4_4(X47,X48,X49,X50)!=X49|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49)))&(r2_hidden(esk4_4(X47,X48,X49,X50),X50)|(esk4_4(X47,X48,X49,X50)=X47|esk4_4(X47,X48,X49,X50)=X48|esk4_4(X47,X48,X49,X50)=X49)|X50=k1_enumset1(X47,X48,X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.15/1.33  cnf(c_0_16, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.15/1.33  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.15/1.33  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.15/1.33  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.15/1.33  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.15/1.33  fof(c_0_21, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.15/1.33  cnf(c_0_22, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.15/1.33  cnf(c_0_23, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.15/1.33  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 1.15/1.33  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.15/1.33  cnf(c_0_26, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 1.15/1.33  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.15/1.33  cnf(c_0_28, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_20])).
% 1.15/1.33  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 1.15/1.33  cnf(c_0_30, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X3,X2))|r2_hidden(esk3_3(X2,X3,X1),X2)|r2_hidden(esk3_3(X2,X3,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 1.15/1.33  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.15/1.33  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_tarski(esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.15/1.33  cnf(c_0_33, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_19])).
% 1.15/1.33  cnf(c_0_34, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.15/1.33  cnf(c_0_35, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_28])).
% 1.15/1.33  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_3(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk6_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])])).
% 1.15/1.33  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_31, c_0_20])).
% 1.15/1.33  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 1.15/1.33  cnf(c_0_39, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 1.15/1.33  cnf(c_0_40, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_34, c_0_19])).
% 1.15/1.33  cnf(c_0_41, negated_conjecture, (esk3_3(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.15/1.33  cnf(c_0_42, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 1.15/1.33  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_38, c_0_25])).
% 1.15/1.33  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.15/1.33  cnf(c_0_45, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 1.15/1.33  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25]), c_0_42])]), c_0_43])).
% 1.15/1.33  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_44, c_0_20])).
% 1.15/1.33  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.15/1.33  cnf(c_0_49, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 1.15/1.33  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_46])])).
% 1.15/1.33  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), ['proof']).
% 1.15/1.33  # SZS output end CNFRefutation
% 1.15/1.33  # Proof object total steps             : 52
% 1.15/1.33  # Proof object clause steps            : 35
% 1.15/1.33  # Proof object formula steps           : 17
% 1.15/1.33  # Proof object conjectures             : 15
% 1.15/1.33  # Proof object clause conjectures      : 12
% 1.15/1.33  # Proof object formula conjectures     : 3
% 1.15/1.33  # Proof object initial clauses used    : 13
% 1.15/1.33  # Proof object initial formulas used   : 8
% 1.15/1.33  # Proof object generating inferences   : 7
% 1.15/1.33  # Proof object simplifying inferences  : 39
% 1.15/1.33  # Training examples: 0 positive, 0 negative
% 1.15/1.33  # Parsed axioms                        : 15
% 1.15/1.33  # Removed by relevancy pruning/SinE    : 0
% 1.15/1.33  # Initial clauses                      : 38
% 1.15/1.33  # Removed in clause preprocessing      : 4
% 1.15/1.33  # Initial clauses in saturation        : 34
% 1.15/1.33  # Processed clauses                    : 3506
% 1.15/1.33  # ...of these trivial                  : 131
% 1.15/1.33  # ...subsumed                          : 2767
% 1.15/1.33  # ...remaining for further processing  : 608
% 1.15/1.33  # Other redundant clauses eliminated   : 3414
% 1.15/1.33  # Clauses deleted for lack of memory   : 0
% 1.15/1.33  # Backward-subsumed                    : 2
% 1.15/1.33  # Backward-rewritten                   : 76
% 1.15/1.33  # Generated clauses                    : 92965
% 1.15/1.33  # ...of the previous two non-trivial   : 82000
% 1.15/1.33  # Contextual simplify-reflections      : 9
% 1.15/1.33  # Paramodulations                      : 89530
% 1.15/1.33  # Factorizations                       : 24
% 1.15/1.33  # Equation resolutions                 : 3414
% 1.15/1.33  # Propositional unsat checks           : 0
% 1.15/1.33  #    Propositional check models        : 0
% 1.15/1.33  #    Propositional check unsatisfiable : 0
% 1.15/1.33  #    Propositional clauses             : 0
% 1.15/1.33  #    Propositional clauses after purity: 0
% 1.15/1.33  #    Propositional unsat core size     : 0
% 1.15/1.33  #    Propositional preprocessing time  : 0.000
% 1.15/1.33  #    Propositional encoding time       : 0.000
% 1.15/1.33  #    Propositional solver time         : 0.000
% 1.15/1.33  #    Success case prop preproc time    : 0.000
% 1.15/1.33  #    Success case prop encoding time   : 0.000
% 1.15/1.33  #    Success case prop solver time     : 0.000
% 1.15/1.33  # Current number of processed clauses  : 485
% 1.15/1.33  #    Positive orientable unit clauses  : 47
% 1.15/1.33  #    Positive unorientable unit clauses: 1
% 1.15/1.33  #    Negative unit clauses             : 3
% 1.15/1.33  #    Non-unit-clauses                  : 434
% 1.15/1.33  # Current number of unprocessed clauses: 78174
% 1.15/1.33  # ...number of literals in the above   : 373675
% 1.15/1.33  # Current number of archived formulas  : 0
% 1.15/1.33  # Current number of archived clauses   : 115
% 1.15/1.33  # Clause-clause subsumption calls (NU) : 118708
% 1.15/1.33  # Rec. Clause-clause subsumption calls : 71455
% 1.15/1.33  # Non-unit clause-clause subsumptions  : 2095
% 1.15/1.33  # Unit Clause-clause subsumption calls : 4022
% 1.15/1.33  # Rewrite failures with RHS unbound    : 0
% 1.15/1.33  # BW rewrite match attempts            : 62
% 1.15/1.33  # BW rewrite match successes           : 22
% 1.15/1.33  # Condensation attempts                : 0
% 1.15/1.33  # Condensation successes               : 0
% 1.15/1.33  # Termbank termtop insertions          : 1895778
% 1.15/1.34  
% 1.15/1.34  # -------------------------------------------------
% 1.15/1.34  # User time                : 0.947 s
% 1.15/1.34  # System time              : 0.039 s
% 1.15/1.34  # Total time               : 0.986 s
% 1.15/1.34  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
