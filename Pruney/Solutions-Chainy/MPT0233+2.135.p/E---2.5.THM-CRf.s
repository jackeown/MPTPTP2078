%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  63 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 182 expanded)
%              Number of equality atoms :   74 ( 101 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))
    & esk4_0 != esk6_0
    & esk4_0 != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16] : r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15]),c_0_16]),c_0_16])).

fof(c_0_20,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X30
        | X33 = X31
        | X32 != k2_tarski(X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k2_tarski(X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k2_tarski(X30,X31) )
      & ( esk3_3(X35,X36,X37) != X35
        | ~ r2_hidden(esk3_3(X35,X36,X37),X37)
        | X37 = k2_tarski(X35,X36) )
      & ( esk3_3(X35,X36,X37) != X36
        | ~ r2_hidden(esk3_3(X35,X36,X37),X37)
        | X37 = k2_tarski(X35,X36) )
      & ( r2_hidden(esk3_3(X35,X36,X37),X37)
        | esk3_3(X35,X36,X37) = X35
        | esk3_3(X35,X36,X37) = X36
        | X37 = k2_tarski(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0)) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X19
        | X23 = X20
        | X23 = X21
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X19
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X25,X26,X27,X28) != X25
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X26
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X27
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | esk2_4(X25,X26,X27,X28) = X25
        | esk2_4(X25,X26,X27,X28) = X26
        | esk2_4(X25,X26,X27,X28) = X27
        | X28 = k1_enumset1(X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( r2_hidden(X6,X7)
        | r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X6,X7)
        | r2_hidden(X6,X8)
        | r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X6,X8)
        | r2_hidden(X6,X7)
        | r2_hidden(X6,k5_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0)))
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_34,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0))
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk7_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.37  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.20/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.37  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.20/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.20/0.37  fof(c_0_10, negated_conjecture, ((r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))&esk4_0!=esk6_0)&esk4_0!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.37  fof(c_0_11, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_12, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  fof(c_0_13, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  fof(c_0_17, plain, ![X15, X16]:r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.20/0.37  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.20/0.37  fof(c_0_20, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X33,X32)|(X33=X30|X33=X31)|X32!=k2_tarski(X30,X31))&((X34!=X30|r2_hidden(X34,X32)|X32!=k2_tarski(X30,X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k2_tarski(X30,X31))))&(((esk3_3(X35,X36,X37)!=X35|~r2_hidden(esk3_3(X35,X36,X37),X37)|X37=k2_tarski(X35,X36))&(esk3_3(X35,X36,X37)!=X36|~r2_hidden(esk3_3(X35,X36,X37),X37)|X37=k2_tarski(X35,X36)))&(r2_hidden(esk3_3(X35,X36,X37),X37)|(esk3_3(X35,X36,X37)=X35|esk3_3(X35,X36,X37)=X36)|X37=k2_tarski(X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.37  fof(c_0_21, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.37  cnf(c_0_22, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0))=k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.37  fof(c_0_24, plain, ![X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X23,X22)|(X23=X19|X23=X20|X23=X21)|X22!=k1_enumset1(X19,X20,X21))&(((X24!=X19|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))&(X24!=X20|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21)))&(X24!=X21|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))))&((((esk2_4(X25,X26,X27,X28)!=X25|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27))&(esk2_4(X25,X26,X27,X28)!=X26|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(esk2_4(X25,X26,X27,X28)!=X27|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(r2_hidden(esk2_4(X25,X26,X27,X28),X28)|(esk2_4(X25,X26,X27,X28)=X25|esk2_4(X25,X26,X27,X28)=X26|esk2_4(X25,X26,X27,X28)=X27)|X28=k1_enumset1(X25,X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.37  cnf(c_0_25, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.37  fof(c_0_28, plain, ![X6, X7, X8]:(((~r2_hidden(X6,X7)|~r2_hidden(X6,X8)|~r2_hidden(X6,k5_xboole_0(X7,X8)))&(r2_hidden(X6,X7)|r2_hidden(X6,X8)|~r2_hidden(X6,k5_xboole_0(X7,X8))))&((~r2_hidden(X6,X7)|r2_hidden(X6,X8)|r2_hidden(X6,k5_xboole_0(X7,X8)))&(~r2_hidden(X6,X8)|r2_hidden(X6,X7)|r2_hidden(X6,k5_xboole_0(X7,X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.20/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_30, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_16])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0)))|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_32, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X2,X5)), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 0.20/0.37  cnf(c_0_34, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk7_0))|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.37  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (X1=esk7_0|X1=esk6_0|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.37  cnf(c_0_38, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (esk4_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 42
% 0.20/0.37  # Proof object clause steps            : 23
% 0.20/0.37  # Proof object formula steps           : 19
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 9
% 0.20/0.37  # Proof object generating inferences   : 8
% 0.20/0.37  # Proof object simplifying inferences  : 10
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 9
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 28
% 0.20/0.37  # Removed in clause preprocessing      : 2
% 0.20/0.37  # Initial clauses in saturation        : 26
% 0.20/0.37  # Processed clauses                    : 63
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 3
% 0.20/0.37  # ...remaining for further processing  : 60
% 0.20/0.37  # Other redundant clauses eliminated   : 5
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 46
% 0.20/0.37  # ...of the previous two non-trivial   : 37
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 37
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 9
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 31
% 0.20/0.37  #    Positive orientable unit clauses  : 8
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 21
% 0.20/0.37  # Current number of unprocessed clauses: 21
% 0.20/0.37  # ...number of literals in the above   : 65
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 26
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 101
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 92
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 6
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2403
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.030 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
