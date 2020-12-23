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
% DateTime   : Thu Dec  3 10:51:27 EST 2020

% Result     : Theorem 0.06s
% Output     : CNFRefutation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  67 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 117 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r1_xboole_0(X5,X6)
        | r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X15] : r1_xboole_0(X15,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X16,X17,X20,X22,X23] :
      ( ( ~ v1_relat_1(X16)
        | ~ r2_hidden(X17,X16)
        | X17 = k4_tarski(esk2_2(X16,X17),esk3_2(X16,X17)) )
      & ( r2_hidden(esk4_1(X20),X20)
        | v1_relat_1(X20) )
      & ( esk4_1(X20) != k4_tarski(X22,X23)
        | v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k10_relat_1(X25,X24) = k10_relat_1(X25,k3_xboole_0(k2_relat_1(X25),X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(X26,k2_relat_1(X26)) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_24,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_28,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_31,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_34,plain,
    ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k10_relat_1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_30]),c_0_28])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(k1_xboole_0,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n003.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 20:01:27 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.06/0.27  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S059A
% 0.06/0.27  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.06/0.27  #
% 0.06/0.27  # Preprocessing time       : 0.012 s
% 0.06/0.27  # Presaturation interreduction done
% 0.06/0.27  
% 0.06/0.27  # Proof found!
% 0.06/0.27  # SZS status Theorem
% 0.06/0.27  # SZS output start CNFRefutation
% 0.06/0.27  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.06/0.27  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.06/0.27  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.06/0.27  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.06/0.27  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.06/0.27  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.06/0.27  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.06/0.27  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.06/0.27  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.06/0.27  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.06/0.27  fof(c_0_10, plain, ![X5, X6, X8, X9, X10]:((r1_xboole_0(X5,X6)|r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)))&(~r2_hidden(X10,k3_xboole_0(X8,X9))|~r1_xboole_0(X8,X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.06/0.27  fof(c_0_11, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.06/0.27  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.06/0.27  cnf(c_0_13, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.06/0.27  fof(c_0_14, plain, ![X15]:r1_xboole_0(X15,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.06/0.27  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.06/0.27  cnf(c_0_16, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.06/0.27  fof(c_0_17, plain, ![X16, X17, X20, X22, X23]:((~v1_relat_1(X16)|(~r2_hidden(X17,X16)|X17=k4_tarski(esk2_2(X16,X17),esk3_2(X16,X17))))&((r2_hidden(esk4_1(X20),X20)|v1_relat_1(X20))&(esk4_1(X20)!=k4_tarski(X22,X23)|v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.06/0.27  fof(c_0_18, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.06/0.27  fof(c_0_19, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.06/0.27  fof(c_0_20, plain, ![X24, X25]:(~v1_relat_1(X25)|k10_relat_1(X25,X24)=k10_relat_1(X25,k3_xboole_0(k2_relat_1(X25),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.06/0.27  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])])).
% 0.06/0.27  cnf(c_0_22, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.06/0.27  fof(c_0_23, plain, ![X26]:(~v1_relat_1(X26)|k10_relat_1(X26,k2_relat_1(X26))=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.06/0.27  fof(c_0_24, negated_conjecture, k10_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.06/0.27  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.06/0.27  cnf(c_0_26, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.06/0.27  cnf(c_0_27, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.06/0.27  cnf(c_0_28, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.06/0.27  cnf(c_0_29, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.06/0.27  cnf(c_0_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.06/0.27  fof(c_0_31, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.06/0.27  cnf(c_0_32, negated_conjecture, (k10_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.06/0.27  cnf(c_0_33, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.06/0.27  cnf(c_0_34, plain, (k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k10_relat_1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.06/0.27  cnf(c_0_35, plain, (k10_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_30]), c_0_28])])).
% 0.06/0.27  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.06/0.27  cnf(c_0_37, negated_conjecture, (~r1_tarski(k10_relat_1(k1_xboole_0,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.06/0.27  cnf(c_0_38, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_35]), c_0_36])])).
% 0.06/0.27  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_36])]), ['proof']).
% 0.06/0.27  # SZS output end CNFRefutation
% 0.06/0.27  # Proof object total steps             : 40
% 0.06/0.27  # Proof object clause steps            : 20
% 0.06/0.27  # Proof object formula steps           : 20
% 0.06/0.27  # Proof object conjectures             : 6
% 0.06/0.27  # Proof object clause conjectures      : 3
% 0.06/0.27  # Proof object formula conjectures     : 3
% 0.06/0.27  # Proof object initial clauses used    : 11
% 0.06/0.27  # Proof object initial formulas used   : 10
% 0.06/0.27  # Proof object generating inferences   : 7
% 0.06/0.27  # Proof object simplifying inferences  : 13
% 0.06/0.27  # Training examples: 0 positive, 0 negative
% 0.06/0.27  # Parsed axioms                        : 10
% 0.06/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.27  # Initial clauses                      : 14
% 0.06/0.27  # Removed in clause preprocessing      : 0
% 0.06/0.27  # Initial clauses in saturation        : 14
% 0.06/0.27  # Processed clauses                    : 68
% 0.06/0.27  # ...of these trivial                  : 0
% 0.06/0.27  # ...subsumed                          : 21
% 0.06/0.27  # ...remaining for further processing  : 47
% 0.06/0.27  # Other redundant clauses eliminated   : 1
% 0.06/0.27  # Clauses deleted for lack of memory   : 0
% 0.06/0.27  # Backward-subsumed                    : 0
% 0.06/0.27  # Backward-rewritten                   : 6
% 0.06/0.27  # Generated clauses                    : 86
% 0.06/0.27  # ...of the previous two non-trivial   : 70
% 0.06/0.27  # Contextual simplify-reflections      : 0
% 0.06/0.27  # Paramodulations                      : 85
% 0.06/0.27  # Factorizations                       : 0
% 0.06/0.27  # Equation resolutions                 : 1
% 0.06/0.27  # Propositional unsat checks           : 0
% 0.06/0.27  #    Propositional check models        : 0
% 0.06/0.27  #    Propositional check unsatisfiable : 0
% 0.06/0.27  #    Propositional clauses             : 0
% 0.06/0.27  #    Propositional clauses after purity: 0
% 0.06/0.27  #    Propositional unsat core size     : 0
% 0.06/0.27  #    Propositional preprocessing time  : 0.000
% 0.06/0.27  #    Propositional encoding time       : 0.000
% 0.06/0.27  #    Propositional solver time         : 0.000
% 0.06/0.27  #    Success case prop preproc time    : 0.000
% 0.06/0.27  #    Success case prop encoding time   : 0.000
% 0.06/0.27  #    Success case prop solver time     : 0.000
% 0.06/0.27  # Current number of processed clauses  : 27
% 0.06/0.27  #    Positive orientable unit clauses  : 7
% 0.06/0.27  #    Positive unorientable unit clauses: 0
% 0.06/0.27  #    Negative unit clauses             : 2
% 0.06/0.27  #    Non-unit-clauses                  : 18
% 0.06/0.27  # Current number of unprocessed clauses: 29
% 0.06/0.27  # ...number of literals in the above   : 78
% 0.06/0.27  # Current number of archived formulas  : 0
% 0.06/0.27  # Current number of archived clauses   : 20
% 0.06/0.27  # Clause-clause subsumption calls (NU) : 70
% 0.06/0.27  # Rec. Clause-clause subsumption calls : 54
% 0.06/0.27  # Non-unit clause-clause subsumptions  : 6
% 0.06/0.27  # Unit Clause-clause subsumption calls : 5
% 0.06/0.27  # Rewrite failures with RHS unbound    : 0
% 0.06/0.27  # BW rewrite match attempts            : 6
% 0.06/0.27  # BW rewrite match successes           : 6
% 0.06/0.27  # Condensation attempts                : 0
% 0.06/0.27  # Condensation successes               : 0
% 0.06/0.27  # Termbank termtop insertions          : 1436
% 0.06/0.27  
% 0.06/0.27  # -------------------------------------------------
% 0.06/0.27  # User time                : 0.014 s
% 0.06/0.27  # System time              : 0.000 s
% 0.06/0.27  # Total time               : 0.015 s
% 0.06/0.27  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
