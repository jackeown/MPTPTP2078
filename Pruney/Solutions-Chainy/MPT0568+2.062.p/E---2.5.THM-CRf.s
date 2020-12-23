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
% DateTime   : Thu Dec  3 10:51:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 109 expanded)
%              Number of clauses        :   22 (  55 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 337 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(c_0_6,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X23] :
      ( ( r2_hidden(esk6_3(X19,X20,X21),k2_relat_1(X21))
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(X19,esk6_3(X19,X20,X21)),X21)
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk6_3(X19,X20,X21),X20)
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X23,k2_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X23),X21)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_8,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk2_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_11,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X11,X12,X15,X17,X18] :
      ( ( ~ v1_relat_1(X11)
        | ~ r2_hidden(X12,X11)
        | X12 = k4_tarski(esk3_2(X11,X12),esk4_2(X11,X12)) )
      & ( r2_hidden(esk5_1(X15),X15)
        | v1_relat_1(X15) )
      & ( esk5_1(X15) != k4_tarski(X17,X18)
        | v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_16,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_16])).

cnf(c_0_19,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_17]),c_0_15])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_22,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( v1_relat_1(k10_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v1_relat_1(k10_relat_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

fof(c_0_28,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_12])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 0.19/0.37  fof(c_0_6, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X19, X20, X21, X23]:((((r2_hidden(esk6_3(X19,X20,X21),k2_relat_1(X21))|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21))&(r2_hidden(k4_tarski(X19,esk6_3(X19,X20,X21)),X21)|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21)))&(r2_hidden(esk6_3(X19,X20,X21),X20)|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21)))&(~r2_hidden(X23,k2_relat_1(X21))|~r2_hidden(k4_tarski(X19,X23),X21)|~r2_hidden(X23,X20)|r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.37  cnf(c_0_8, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_10, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk2_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.37  cnf(c_0_11, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.37  cnf(c_0_12, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_13, plain, ![X11, X12, X15, X17, X18]:((~v1_relat_1(X11)|(~r2_hidden(X12,X11)|X12=k4_tarski(esk3_2(X11,X12),esk4_2(X11,X12))))&((r2_hidden(esk5_1(X15),X15)|v1_relat_1(X15))&(esk5_1(X15)!=k4_tarski(X17,X18)|v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.37  cnf(c_0_14, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_15, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_16, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_17, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_18, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_8, c_0_16])).
% 0.19/0.37  cnf(c_0_19, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_17]), c_0_15])])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk6_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_21, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.19/0.37  cnf(c_0_22, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(k1_xboole_0,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.19/0.37  cnf(c_0_23, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_24, plain, (v1_relat_1(k10_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.19/0.37  fof(c_0_25, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.19/0.37  cnf(c_0_26, plain, (v1_xboole_0(k10_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_27, plain, (v1_relat_1(k10_relat_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.19/0.37  fof(c_0_28, negated_conjecture, k10_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.37  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_8, c_0_12])).
% 0.19/0.37  cnf(c_0_30, plain, (v1_xboole_0(k10_relat_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k10_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_32, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 34
% 0.19/0.37  # Proof object clause steps            : 22
% 0.19/0.37  # Proof object formula steps           : 12
% 0.19/0.37  # Proof object conjectures             : 5
% 0.19/0.37  # Proof object clause conjectures      : 2
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 13
% 0.19/0.37  # Proof object simplifying inferences  : 6
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 12
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 12
% 0.19/0.37  # Processed clauses                    : 68
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 25
% 0.19/0.37  # ...remaining for further processing  : 43
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 2
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 151
% 0.19/0.37  # ...of the previous two non-trivial   : 105
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 150
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 35
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 32
% 0.19/0.37  # Current number of unprocessed clauses: 42
% 0.19/0.37  # ...number of literals in the above   : 200
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 8
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 341
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 221
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 27
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 5
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2671
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.032 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
