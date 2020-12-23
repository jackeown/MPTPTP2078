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
% DateTime   : Thu Dec  3 10:52:37 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of clauses        :   24 (  30 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 157 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t214_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t214_relat_1])).

fof(c_0_11,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | r1_tarski(k1_relat_1(k3_xboole_0(X15,X16)),k3_xboole_0(k1_relat_1(X15),k1_relat_1(X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k4_xboole_0(X11,X12) = X11 )
      & ( k4_xboole_0(X11,X12) != X11
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))
    & ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( k4_xboole_0(X5,X6) != k1_xboole_0
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | k4_xboole_0(X5,X6) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) = k1_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X17] :
      ( ( k1_relat_1(X17) != k1_xboole_0
        | X17 = k1_xboole_0
        | ~ v1_relat_1(X17) )
      & ( k2_relat_1(X17) != k1_xboole_0
        | X17 = k1_xboole_0
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_34,plain,(
    ! [X3,X4] :
      ( ( ~ r1_xboole_0(X3,X4)
        | k3_xboole_0(X3,X4) = k1_xboole_0 )
      & ( k3_xboole_0(X3,X4) != k1_xboole_0
        | r1_xboole_0(X3,X4) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23])).

cnf(c_0_37,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.14/0.37  # and selection function SelectCQPrecWNTNp.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t214_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 0.14/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.37  fof(t14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 0.14/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.14/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.14/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.14/0.37  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.14/0.37  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.14/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t214_relat_1])).
% 0.14/0.37  fof(c_0_11, plain, ![X7]:k3_xboole_0(X7,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.37  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.37  fof(c_0_13, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|r1_tarski(k1_relat_1(k3_xboole_0(X15,X16)),k3_xboole_0(k1_relat_1(X15),k1_relat_1(X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).
% 0.14/0.37  fof(c_0_14, plain, ![X11, X12]:((~r1_xboole_0(X11,X12)|k4_xboole_0(X11,X12)=X11)&(k4_xboole_0(X11,X12)!=X11|r1_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.14/0.37  fof(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))&~r1_xboole_0(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.14/0.37  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  fof(c_0_18, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.37  cnf(c_0_19, plain, (r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  fof(c_0_24, plain, ![X5, X6]:((k4_xboole_0(X5,X6)!=k1_xboole_0|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|k4_xboole_0(X5,X6)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.14/0.37  cnf(c_0_25, plain, (r1_tarski(k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_17])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))=k1_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_27, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  fof(c_0_30, plain, ![X17]:((k1_relat_1(X17)!=k1_xboole_0|X17=k1_xboole_0|~v1_relat_1(X17))&(k2_relat_1(X17)!=k1_xboole_0|X17=k1_xboole_0|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.14/0.37  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.14/0.37  fof(c_0_33, plain, ![X13, X14]:(~v1_relat_1(X13)|v1_relat_1(k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.14/0.37  fof(c_0_34, plain, ![X3, X4]:((~r1_xboole_0(X3,X4)|k3_xboole_0(X3,X4)=k1_xboole_0)&(k3_xboole_0(X3,X4)!=k1_xboole_0|r1_xboole_0(X3,X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.14/0.37  cnf(c_0_35, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (k1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_23])).
% 0.14/0.37  cnf(c_0_37, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.37  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0|~v1_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.37  cnf(c_0_40, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_37, c_0_17])).
% 0.14/0.37  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_17])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29])])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 45
% 0.14/0.37  # Proof object clause steps            : 24
% 0.14/0.37  # Proof object formula steps           : 21
% 0.14/0.37  # Proof object conjectures             : 13
% 0.14/0.37  # Proof object clause conjectures      : 10
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 13
% 0.14/0.37  # Proof object initial formulas used   : 10
% 0.14/0.37  # Proof object generating inferences   : 6
% 0.14/0.37  # Proof object simplifying inferences  : 14
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 10
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 17
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 16
% 0.14/0.37  # Processed clauses                    : 47
% 0.14/0.37  # ...of these trivial                  : 4
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 43
% 0.14/0.37  # Other redundant clauses eliminated   : 3
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 2
% 0.14/0.37  # Backward-rewritten                   : 3
% 0.14/0.37  # Generated clauses                    : 44
% 0.14/0.37  # ...of the previous two non-trivial   : 29
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 41
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 3
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 22
% 0.14/0.37  #    Positive orientable unit clauses  : 10
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 11
% 0.14/0.37  # Current number of unprocessed clauses: 5
% 0.14/0.37  # ...number of literals in the above   : 15
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 22
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 14
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 13
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.37  # Unit Clause-clause subsumption calls : 5
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 11
% 0.14/0.37  # BW rewrite match successes           : 3
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1434
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.027 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.032 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
