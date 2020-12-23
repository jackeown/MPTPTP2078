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
% DateTime   : Thu Dec  3 10:51:57 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 103 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t187_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r1_xboole_0(X2,k1_relat_1(X1))
           => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t187_relat_1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_xboole_0(X9,k4_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_10,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k1_relat_1(k7_relat_1(X13,X12)),k1_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_xboole_0(esk2_0,k1_relat_1(esk1_0))
    & k7_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_23,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,k1_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k1_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk2_0,k1_relat_1(esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X14,X15] :
      ( ( k7_relat_1(X15,X14) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X15),X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_xboole_0(k1_relat_1(X15),X14)
        | k7_relat_1(X15,X14) = k1_xboole_0
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:03:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.21/0.37  # and selection function SelectComplexG.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.028 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t187_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.21/0.37  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.21/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.37  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 0.21/0.37  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.37  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.21/0.37  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.21/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t187_relat_1])).
% 0.21/0.37  fof(c_0_9, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_xboole_0(X9,k4_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.21/0.37  fof(c_0_10, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.37  fof(c_0_11, plain, ![X12, X13]:(~v1_relat_1(X13)|r1_tarski(k1_relat_1(k7_relat_1(X13,X12)),k1_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.21/0.37  fof(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)&(r1_xboole_0(esk2_0,k1_relat_1(esk1_0))&k7_relat_1(esk1_0,esk2_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.37  cnf(c_0_13, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.37  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.37  cnf(c_0_15, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.37  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  fof(c_0_17, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.37  cnf(c_0_18, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.37  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.37  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk2_0,k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  fof(c_0_22, plain, ![X8]:k5_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.37  fof(c_0_23, plain, ![X16]:(~v1_relat_1(X16)|k7_relat_1(X16,k1_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.21/0.37  cnf(c_0_24, negated_conjecture, (r1_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k1_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.37  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk2_0,k1_relat_1(esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.37  cnf(c_0_26, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.37  cnf(c_0_27, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.37  fof(c_0_28, plain, ![X14, X15]:((k7_relat_1(X15,X14)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X15),X14)|~v1_relat_1(X15))&(~r1_xboole_0(k1_relat_1(X15),X14)|k7_relat_1(X15,X14)=k1_xboole_0|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.21/0.37  cnf(c_0_29, negated_conjecture, (r1_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.21/0.37  cnf(c_0_30, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 0.21/0.37  cnf(c_0_31, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.37  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k1_relat_1(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.37  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16])]), c_0_33]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 35
% 0.21/0.37  # Proof object clause steps            : 18
% 0.21/0.37  # Proof object formula steps           : 17
% 0.21/0.37  # Proof object conjectures             : 13
% 0.21/0.37  # Proof object clause conjectures      : 10
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 10
% 0.21/0.37  # Proof object initial formulas used   : 8
% 0.21/0.37  # Proof object generating inferences   : 7
% 0.21/0.37  # Proof object simplifying inferences  : 5
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 8
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 12
% 0.21/0.37  # Removed in clause preprocessing      : 1
% 0.21/0.37  # Initial clauses in saturation        : 11
% 0.21/0.37  # Processed clauses                    : 30
% 0.21/0.37  # ...of these trivial                  : 0
% 0.21/0.37  # ...subsumed                          : 0
% 0.21/0.37  # ...remaining for further processing  : 30
% 0.21/0.37  # Other redundant clauses eliminated   : 0
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 0
% 0.21/0.37  # Generated clauses                    : 17
% 0.21/0.37  # ...of the previous two non-trivial   : 15
% 0.21/0.37  # Contextual simplify-reflections      : 0
% 0.21/0.37  # Paramodulations                      : 17
% 0.21/0.37  # Factorizations                       : 0
% 0.21/0.37  # Equation resolutions                 : 0
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 19
% 0.21/0.37  #    Positive orientable unit clauses  : 10
% 0.21/0.37  #    Positive unorientable unit clauses: 0
% 0.21/0.37  #    Negative unit clauses             : 1
% 0.21/0.37  #    Non-unit-clauses                  : 8
% 0.21/0.37  # Current number of unprocessed clauses: 6
% 0.21/0.37  # ...number of literals in the above   : 8
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 12
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 10
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 10
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.37  # Unit Clause-clause subsumption calls : 0
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 0
% 0.21/0.37  # BW rewrite match successes           : 0
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 884
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.028 s
% 0.21/0.37  # System time              : 0.004 s
% 0.21/0.37  # Total time               : 0.032 s
% 0.21/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
