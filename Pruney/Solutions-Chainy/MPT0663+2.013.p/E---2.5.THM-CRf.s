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
% DateTime   : Thu Dec  3 10:54:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 136 expanded)
%              Number of clauses        :   27 (  61 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 329 expanded)
%              Number of equality atoms :   31 ( 129 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

fof(c_0_9,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))
    & k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),k4_xboole_0(k1_relat_1(esk4_0),esk3_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),X1))
    | r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,X24)
        | ~ r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(X23,k1_relat_1(X25))
        | ~ r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X23,k1_relat_1(X25))
        | r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk2_0,k4_xboole_0(X2,k4_xboole_0(k1_relat_1(esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ r2_hidden(X26,k1_relat_1(k7_relat_1(X28,X27)))
      | k1_funct_1(k7_relat_1(X28,X27),X26) = k1_funct_1(X28,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(k7_relat_1(X1,esk3_0)))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_0,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_38])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.29  % Computer   : n022.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 17:34:10 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  # Version: 2.5pre002
% 0.09/0.29  # No SInE strategy applied
% 0.09/0.29  # Trying AutoSched0 for 299 seconds
% 0.13/0.32  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.32  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.32  #
% 0.13/0.32  # Preprocessing time       : 0.027 s
% 0.13/0.32  # Presaturation interreduction done
% 0.13/0.32  
% 0.13/0.32  # Proof found!
% 0.13/0.32  # SZS status Theorem
% 0.13/0.32  # SZS output start CNFRefutation
% 0.13/0.32  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 0.13/0.32  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.32  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.32  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.32  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.32  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.13/0.32  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.13/0.32  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.13/0.32  fof(c_0_9, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.32  fof(c_0_10, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.32  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))&k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0)!=k1_funct_1(esk4_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.32  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.32  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.32  fof(c_0_14, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.32  fof(c_0_15, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.32  fof(c_0_16, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.32  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.32  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.32  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.32  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.32  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.32  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.32  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_19])).
% 0.13/0.32  cnf(c_0_24, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.32  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.32  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),k4_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.32  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.32  cnf(c_0_28, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.32  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.32  cnf(c_0_30, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.32  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),X1))|r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.32  fof(c_0_32, plain, ![X23, X24, X25]:(((r2_hidden(X23,X24)|~r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25))&(r2_hidden(X23,k1_relat_1(X25))|~r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25)))&(~r2_hidden(X23,X24)|~r2_hidden(X23,k1_relat_1(X25))|r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.13/0.32  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,X1)|~r2_hidden(esk2_0,k4_xboole_0(X2,k4_xboole_0(k1_relat_1(esk4_0),X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.32  cnf(c_0_34, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.32  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.13/0.32  fof(c_0_36, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~r2_hidden(X26,k1_relat_1(k7_relat_1(X28,X27)))|k1_funct_1(k7_relat_1(X28,X27),X26)=k1_funct_1(X28,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.13/0.32  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(k7_relat_1(X1,esk3_0)))|~v1_relat_1(X1)|~r2_hidden(esk2_0,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.32  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.32  cnf(c_0_39, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.32  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_38])])).
% 0.13/0.32  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.32  cnf(c_0_42, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0)!=k1_funct_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.32  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_38])]), c_0_42]), ['proof']).
% 0.13/0.32  # SZS output end CNFRefutation
% 0.13/0.32  # Proof object total steps             : 44
% 0.13/0.32  # Proof object clause steps            : 27
% 0.13/0.32  # Proof object formula steps           : 17
% 0.13/0.32  # Proof object conjectures             : 16
% 0.13/0.32  # Proof object clause conjectures      : 13
% 0.13/0.32  # Proof object formula conjectures     : 3
% 0.13/0.32  # Proof object initial clauses used    : 13
% 0.13/0.32  # Proof object initial formulas used   : 8
% 0.13/0.32  # Proof object generating inferences   : 7
% 0.13/0.32  # Proof object simplifying inferences  : 15
% 0.13/0.32  # Training examples: 0 positive, 0 negative
% 0.13/0.32  # Parsed axioms                        : 8
% 0.13/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.32  # Initial clauses                      : 18
% 0.13/0.32  # Removed in clause preprocessing      : 3
% 0.13/0.32  # Initial clauses in saturation        : 15
% 0.13/0.32  # Processed clauses                    : 62
% 0.13/0.32  # ...of these trivial                  : 0
% 0.13/0.32  # ...subsumed                          : 2
% 0.13/0.32  # ...remaining for further processing  : 60
% 0.13/0.32  # Other redundant clauses eliminated   : 3
% 0.13/0.32  # Clauses deleted for lack of memory   : 0
% 0.13/0.32  # Backward-subsumed                    : 0
% 0.13/0.32  # Backward-rewritten                   : 1
% 0.13/0.32  # Generated clauses                    : 99
% 0.13/0.32  # ...of the previous two non-trivial   : 70
% 0.13/0.32  # Contextual simplify-reflections      : 0
% 0.13/0.32  # Paramodulations                      : 94
% 0.13/0.32  # Factorizations                       : 2
% 0.13/0.32  # Equation resolutions                 : 3
% 0.13/0.32  # Propositional unsat checks           : 0
% 0.13/0.32  #    Propositional check models        : 0
% 0.13/0.32  #    Propositional check unsatisfiable : 0
% 0.13/0.32  #    Propositional clauses             : 0
% 0.13/0.32  #    Propositional clauses after purity: 0
% 0.13/0.32  #    Propositional unsat core size     : 0
% 0.13/0.32  #    Propositional preprocessing time  : 0.000
% 0.13/0.32  #    Propositional encoding time       : 0.000
% 0.13/0.32  #    Propositional solver time         : 0.000
% 0.13/0.32  #    Success case prop preproc time    : 0.000
% 0.13/0.32  #    Success case prop encoding time   : 0.000
% 0.13/0.32  #    Success case prop solver time     : 0.000
% 0.13/0.32  # Current number of processed clauses  : 41
% 0.13/0.32  #    Positive orientable unit clauses  : 11
% 0.13/0.32  #    Positive unorientable unit clauses: 0
% 0.13/0.32  #    Negative unit clauses             : 6
% 0.13/0.32  #    Non-unit-clauses                  : 24
% 0.13/0.32  # Current number of unprocessed clauses: 35
% 0.13/0.32  # ...number of literals in the above   : 106
% 0.13/0.32  # Current number of archived formulas  : 0
% 0.13/0.32  # Current number of archived clauses   : 19
% 0.13/0.32  # Clause-clause subsumption calls (NU) : 77
% 0.13/0.32  # Rec. Clause-clause subsumption calls : 52
% 0.13/0.32  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.32  # Unit Clause-clause subsumption calls : 31
% 0.13/0.32  # Rewrite failures with RHS unbound    : 0
% 0.13/0.32  # BW rewrite match attempts            : 17
% 0.13/0.32  # BW rewrite match successes           : 1
% 0.13/0.32  # Condensation attempts                : 0
% 0.13/0.32  # Condensation successes               : 0
% 0.13/0.32  # Termbank termtop insertions          : 2781
% 0.13/0.32  
% 0.13/0.32  # -------------------------------------------------
% 0.13/0.32  # User time                : 0.030 s
% 0.13/0.32  # System time              : 0.004 s
% 0.13/0.32  # Total time               : 0.034 s
% 0.13/0.32  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
