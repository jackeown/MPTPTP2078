%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  59 expanded)
%              Number of clauses        :   20 (  29 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 189 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t2_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k3_relat_1(X2))
        | k1_wellord1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_6,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29] :
      ( ( X26 != X24
        | ~ r2_hidden(X26,X25)
        | X25 != k1_wellord1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(X26,X24),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k1_wellord1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( X27 = X24
        | ~ r2_hidden(k4_tarski(X27,X24),X23)
        | r2_hidden(X27,X25)
        | X25 != k1_wellord1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(esk5_3(X23,X28,X29),X29)
        | esk5_3(X23,X28,X29) = X28
        | ~ r2_hidden(k4_tarski(esk5_3(X23,X28,X29),X28),X23)
        | X29 = k1_wellord1(X23,X28)
        | ~ v1_relat_1(X23) )
      & ( esk5_3(X23,X28,X29) != X28
        | r2_hidden(esk5_3(X23,X28,X29),X29)
        | X29 = k1_wellord1(X23,X28)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk5_3(X23,X28,X29),X28),X23)
        | r2_hidden(esk5_3(X23,X28,X29),X29)
        | X29 = k1_wellord1(X23,X28)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,k3_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(X21,k3_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(X11,esk2_3(X9,X10,X11)),X9)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(esk3_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk3_2(X15,X16),X18),X15)
        | X16 = k1_relat_1(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X15)
        | X16 = k1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          | k1_wellord1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t2_wellord1])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ~ r2_hidden(esk6_0,k3_relat_1(esk7_0))
    & k1_wellord1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | v1_xboole_0(k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk7_0))
    | v1_xboole_0(k1_wellord1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(k1_wellord1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_wellord1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k1_wellord1(esk7_0,esk6_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.37  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.37  fof(t2_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k3_relat_1(X2))|k1_wellord1(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 0.20/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.37  fof(c_0_6, plain, ![X23, X24, X25, X26, X27, X28, X29]:((((X26!=X24|~r2_hidden(X26,X25)|X25!=k1_wellord1(X23,X24)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(X26,X24),X23)|~r2_hidden(X26,X25)|X25!=k1_wellord1(X23,X24)|~v1_relat_1(X23)))&(X27=X24|~r2_hidden(k4_tarski(X27,X24),X23)|r2_hidden(X27,X25)|X25!=k1_wellord1(X23,X24)|~v1_relat_1(X23)))&((~r2_hidden(esk5_3(X23,X28,X29),X29)|(esk5_3(X23,X28,X29)=X28|~r2_hidden(k4_tarski(esk5_3(X23,X28,X29),X28),X23))|X29=k1_wellord1(X23,X28)|~v1_relat_1(X23))&((esk5_3(X23,X28,X29)!=X28|r2_hidden(esk5_3(X23,X28,X29),X29)|X29=k1_wellord1(X23,X28)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk5_3(X23,X28,X29),X28),X23)|r2_hidden(esk5_3(X23,X28,X29),X29)|X29=k1_wellord1(X23,X28)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.37  fof(c_0_7, plain, ![X20, X21, X22]:((r2_hidden(X20,k3_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|~v1_relat_1(X22))&(r2_hidden(X21,k3_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.37  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  fof(c_0_9, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:(((~r2_hidden(X11,X10)|r2_hidden(k4_tarski(X11,esk2_3(X9,X10,X11)),X9)|X10!=k1_relat_1(X9))&(~r2_hidden(k4_tarski(X13,X14),X9)|r2_hidden(X13,X10)|X10!=k1_relat_1(X9)))&((~r2_hidden(esk3_2(X15,X16),X16)|~r2_hidden(k4_tarski(esk3_2(X15,X16),X18),X15)|X16=k1_relat_1(X15))&(r2_hidden(esk3_2(X15,X16),X16)|r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X15)|X16=k1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.37  cnf(c_0_11, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_8])).
% 0.20/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k3_relat_1(X2))|k1_wellord1(X2,X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t2_wellord1])).
% 0.20/0.37  cnf(c_0_14, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_16, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_wellord1(X2,X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.37  cnf(c_0_17, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  fof(c_0_18, negated_conjecture, (v1_relat_1(esk7_0)&(~r2_hidden(esk6_0,k3_relat_1(esk7_0))&k1_wellord1(esk7_0,esk6_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.37  cnf(c_0_19, plain, (X1=k1_relat_1(X2)|r2_hidden(esk3_2(X2,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.37  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.37  cnf(c_0_21, plain, (r2_hidden(X1,k3_relat_1(X2))|v1_xboole_0(k1_wellord1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_23, plain, (X1=k1_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk6_0,k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk7_0))|v1_xboole_0(k1_wellord1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_26, plain, (X1=k1_relat_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_14, c_0_23])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (v1_xboole_0(k1_wellord1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (k1_wellord1(esk7_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (k1_wellord1(esk7_0,esk6_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.37  cnf(c_0_31, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_30]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 32
% 0.20/0.37  # Proof object clause steps            : 20
% 0.20/0.37  # Proof object formula steps           : 12
% 0.20/0.37  # Proof object conjectures             : 10
% 0.20/0.37  # Proof object clause conjectures      : 7
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 9
% 0.20/0.37  # Proof object simplifying inferences  : 3
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 18
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 18
% 0.20/0.37  # Processed clauses                    : 60
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 58
% 0.20/0.37  # Other redundant clauses eliminated   : 6
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 68
% 0.20/0.37  # ...of the previous two non-trivial   : 68
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 63
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 6
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
% 0.20/0.37  # Current number of processed clauses  : 33
% 0.20/0.37  #    Positive orientable unit clauses  : 3
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 27
% 0.20/0.37  # Current number of unprocessed clauses: 44
% 0.20/0.37  # ...number of literals in the above   : 144
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 20
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 179
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 98
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2325
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.030 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
