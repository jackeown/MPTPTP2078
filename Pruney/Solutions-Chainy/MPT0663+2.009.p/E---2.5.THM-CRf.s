%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   39 (  84 expanded)
%              Number of clauses        :   22 (  34 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 184 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t198_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k1_relat_1(X1) = k1_relat_1(X2)
               => k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(X11,X10) = k5_relat_1(k6_relat_1(X10),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_9,plain,(
    ! [X12] :
      ( v1_relat_1(k6_relat_1(X12))
      & v1_funct_1(k6_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_10,plain,(
    ! [X13,X14] : k5_relat_1(k6_relat_1(X14),k6_relat_1(X13)) = k6_relat_1(k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k1_relat_1(X6) != k1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X8,X6)) = k1_relat_1(k5_relat_1(X8,X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).

cnf(c_0_12,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X9] :
      ( k1_relat_1(k6_relat_1(X9)) = X9
      & k2_relat_1(k6_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

cnf(c_0_17,plain,
    ( k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X1) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_19,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))
    & k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X3))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_22,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_23,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_22]),c_0_23]),c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk3_0),X1) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ r2_hidden(X15,k1_relat_1(k7_relat_1(X17,X16)))
      | k1_funct_1(k7_relat_1(X17,X16),X15) = k1_funct_1(X17,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(esk2_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(X1,k1_relat_1(esk3_0)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_24])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.13/0.38  # and selection function SelectComplexG.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.13/0.38  fof(t198_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k1_relat_1(X1)=k1_relat_1(X2)=>k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.13/0.38  fof(c_0_8, plain, ![X10, X11]:(~v1_relat_1(X11)|k7_relat_1(X11,X10)=k5_relat_1(k6_relat_1(X10),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.38  fof(c_0_9, plain, ![X12]:(v1_relat_1(k6_relat_1(X12))&v1_funct_1(k6_relat_1(X12))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X13, X14]:k5_relat_1(k6_relat_1(X14),k6_relat_1(X13))=k6_relat_1(k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X6, X7, X8]:(~v1_relat_1(X6)|(~v1_relat_1(X7)|(~v1_relat_1(X8)|(k1_relat_1(X6)!=k1_relat_1(X7)|k1_relat_1(k5_relat_1(X8,X6))=k1_relat_1(k5_relat_1(X8,X7)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).
% 0.13/0.38  cnf(c_0_12, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_15, plain, ![X9]:(k1_relat_1(k6_relat_1(X9))=X9&k2_relat_1(k6_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k1_relat_1(X1)!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k6_relat_1(k3_xboole_0(X1,X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_19, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))&k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k5_relat_1(k6_relat_1(X1),X3))|k1_relat_1(X2)!=k1_relat_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[c_0_14, c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1)|~v1_relat_1(X2)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_22]), c_0_23]), c_0_19])])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_24])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k3_xboole_0(k1_relat_1(esk3_0),X1)=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_27])).
% 0.13/0.38  fof(c_0_31, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~r2_hidden(X15,k1_relat_1(k7_relat_1(X17,X16)))|k1_funct_1(k7_relat_1(X17,X16),X15)=k1_funct_1(X17,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_0,k3_xboole_0(esk2_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k3_xboole_0(X1,k1_relat_1(esk3_0))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_34, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_24])]), c_0_37]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 39
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 13
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 13
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 13
% 0.13/0.38  # Processed clauses                    : 99
% 0.13/0.38  # ...of these trivial                  : 4
% 0.13/0.38  # ...subsumed                          : 23
% 0.13/0.38  # ...remaining for further processing  : 72
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 209
% 0.13/0.38  # ...of the previous two non-trivial   : 171
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 202
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
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
% 0.13/0.38  # Current number of processed clauses  : 55
% 0.13/0.38  #    Positive orientable unit clauses  : 29
% 0.13/0.38  #    Positive unorientable unit clauses: 2
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 98
% 0.13/0.38  # ...number of literals in the above   : 180
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 17
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 72
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 70
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 16
% 0.13/0.38  # BW rewrite match successes           : 12
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3973
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
