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
% DateTime   : Thu Dec  3 10:49:03 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 108 expanded)
%              Number of clauses        :   28 (  49 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  180 ( 437 expanded)
%              Number of equality atoms :   55 ( 131 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,k1_tarski(X12)) != X11
        | ~ r2_hidden(X12,X11) )
      & ( r2_hidden(X12,X11)
        | k4_xboole_0(X11,k1_tarski(X12)) = X11 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_enumset1(X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17,X18,X20,X21,X22,X25] :
      ( ( r2_hidden(k4_tarski(X17,esk1_5(X14,X15,X16,X17,X18)),X14)
        | ~ r2_hidden(k4_tarski(X17,X18),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk1_5(X14,X15,X16,X17,X18),X18),X15)
        | ~ r2_hidden(k4_tarski(X17,X18),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X20,X22),X14)
        | ~ r2_hidden(k4_tarski(X22,X21),X15)
        | r2_hidden(k4_tarski(X20,X21),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)
        | ~ r2_hidden(k4_tarski(esk2_3(X14,X15,X16),X25),X14)
        | ~ r2_hidden(k4_tarski(X25,esk3_3(X14,X15,X16)),X15)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk4_3(X14,X15,X16)),X14)
        | r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk3_3(X14,X15,X16)),X15)
        | r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X29] :
      ( ~ v1_relat_1(X29)
      | r2_hidden(k4_tarski(esk5_1(X29),esk6_1(X29)),X29)
      | X29 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_23,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | v1_relat_1(k5_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | X3 != k5_relat_1(X1,X4)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(k4_tarski(X5,X6),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_31,plain,
    ( X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 != k5_relat_1(k1_xboole_0,X3)
    | X1 != k5_relat_1(X2,X4)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_33,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
      | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,X3)
    | X2 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

fof(c_0_43,plain,(
    ! [X13] :
      ( ~ v1_xboole_0(X13)
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_39])])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:32:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.15/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.027 s
% 0.15/0.38  # Presaturation interreduction done
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.15/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.15/0.38  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.20/0.38  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.20/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.38  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.20/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_10, plain, ![X11, X12]:((k4_xboole_0(X11,k1_tarski(X12))!=X11|~r2_hidden(X12,X11))&(r2_hidden(X12,X11)|k4_xboole_0(X11,k1_tarski(X12))=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_12, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_16, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_enumset1(X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.20/0.38  cnf(c_0_18, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_19, plain, ![X14, X15, X16, X17, X18, X20, X21, X22, X25]:((((r2_hidden(k4_tarski(X17,esk1_5(X14,X15,X16,X17,X18)),X14)|~r2_hidden(k4_tarski(X17,X18),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk1_5(X14,X15,X16,X17,X18),X18),X15)|~r2_hidden(k4_tarski(X17,X18),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(X20,X22),X14)|~r2_hidden(k4_tarski(X22,X21),X15)|r2_hidden(k4_tarski(X20,X21),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14)))&((~r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)|(~r2_hidden(k4_tarski(esk2_3(X14,X15,X16),X25),X14)|~r2_hidden(k4_tarski(X25,esk3_3(X14,X15,X16)),X15))|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&((r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk4_3(X14,X15,X16)),X14)|r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk3_3(X14,X15,X16)),X15)|r2_hidden(k4_tarski(esk2_3(X14,X15,X16),esk3_3(X14,X15,X16)),X16)|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_22, plain, ![X29]:(~v1_relat_1(X29)|(r2_hidden(k4_tarski(esk5_1(X29),esk6_1(X29)),X29)|X29=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.20/0.38  cnf(c_0_23, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  fof(c_0_25, plain, ![X27, X28]:(~v1_relat_1(X27)|~v1_relat_1(X28)|v1_relat_1(k5_relat_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.38  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|X3!=k5_relat_1(X1,X4)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r2_hidden(k4_tarski(X5,X6),X3)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.20/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  fof(c_0_30, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.20/0.38  cnf(c_0_31, plain, (X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.20/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|X2!=k5_relat_1(k1_xboole_0,X3)|X1!=k5_relat_1(X2,X4)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.20/0.38  cnf(c_0_33, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.20/0.38  fof(c_0_34, negated_conjecture, (v1_relat_1(esk7_0)&(k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.20/0.38  cnf(c_0_35, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.20/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,X3)|X2!=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_38, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_29])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_40, plain, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_29])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.38  fof(c_0_43, plain, ![X13]:(~v1_xboole_0(X13)|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_39])])).
% 0.20/0.38  cnf(c_0_45, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_46, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 48
% 0.20/0.38  # Proof object clause steps            : 28
% 0.20/0.38  # Proof object formula steps           : 20
% 0.20/0.38  # Proof object conjectures             : 9
% 0.20/0.38  # Proof object clause conjectures      : 6
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 15
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 45
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 44
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 55
% 0.20/0.38  # ...of the previous two non-trivial   : 39
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 50
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 5
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 27
% 0.20/0.38  #    Positive orientable unit clauses  : 3
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 22
% 0.20/0.38  # Current number of unprocessed clauses: 21
% 0.20/0.38  # ...number of literals in the above   : 149
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 19
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 416
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 38
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.38  # Unit Clause-clause subsumption calls : 13
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2487
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
