%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:03 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  74 expanded)
%              Number of clauses        :   24 (  34 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 257 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,X12)
        | ~ r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13))) )
      & ( X11 != X13
        | ~ r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13))) )
      & ( ~ r2_hidden(X11,X12)
        | X11 = X13
        | r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

fof(c_0_17,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X15,X16,X17,X18,X19,X21,X22,X23,X26] :
      ( ( r2_hidden(k4_tarski(X18,esk1_5(X15,X16,X17,X18,X19)),X15)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk1_5(X15,X16,X17,X18,X19),X19),X16)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X21,X23),X15)
        | ~ r2_hidden(k4_tarski(X23,X22),X16)
        | r2_hidden(k4_tarski(X21,X22),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)
        | ~ r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X26),X15)
        | ~ r2_hidden(k4_tarski(X26,esk3_3(X15,X16,X17)),X16)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk4_3(X15,X16,X17)),X15)
        | r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk3_3(X15,X16,X17)),X16)
        | r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | r2_hidden(k4_tarski(esk5_1(X30),esk6_1(X30)),X30)
      | X30 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_25,plain,
    ( X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | v1_relat_1(k5_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
      | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_38,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_31])).

fof(c_0_39,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.38  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.13/0.38  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.13/0.38  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.13/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(c_0_10, plain, ![X11, X12, X13]:(((r2_hidden(X11,X12)|~r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13))))&(X11!=X13|~r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13)))))&(~r2_hidden(X11,X12)|X11=X13|r2_hidden(X11,k4_xboole_0(X12,k1_tarski(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_12, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  cnf(c_0_13, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.13/0.38  fof(c_0_17, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.38  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1)))), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_20, plain, ![X15, X16, X17, X18, X19, X21, X22, X23, X26]:((((r2_hidden(k4_tarski(X18,esk1_5(X15,X16,X17,X18,X19)),X15)|~r2_hidden(k4_tarski(X18,X19),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk1_5(X15,X16,X17,X18,X19),X19),X16)|~r2_hidden(k4_tarski(X18,X19),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15)))&(~r2_hidden(k4_tarski(X21,X23),X15)|~r2_hidden(k4_tarski(X23,X22),X16)|r2_hidden(k4_tarski(X21,X22),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15)))&((~r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)|(~r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X26),X15)|~r2_hidden(k4_tarski(X26,esk3_3(X15,X16,X17)),X16))|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk4_3(X15,X16,X17)),X15)|r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk3_3(X15,X16,X17)),X16)|r2_hidden(k4_tarski(esk2_3(X15,X16,X17),esk3_3(X15,X16,X17)),X17)|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_23, plain, ![X30]:(~v1_relat_1(X30)|(r2_hidden(k4_tarski(esk5_1(X30),esk6_1(X30)),X30)|X30=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.13/0.38  cnf(c_0_25, plain, (X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_27, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_relat_1(X29)|v1_relat_1(k5_relat_1(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_29, negated_conjecture, (v1_relat_1(esk7_0)&(k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.13/0.38  cnf(c_0_30, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_31, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_31])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_31])).
% 0.13/0.38  fof(c_0_39, plain, ![X14]:(~v1_xboole_0(X14)|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_42, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 44
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 20
% 0.13/0.38  # Proof object conjectures             : 8
% 0.13/0.38  # Proof object clause conjectures      : 5
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 16
% 0.13/0.38  # Processed clauses                    : 46
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 43
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 48
% 0.13/0.38  # ...of the previous two non-trivial   : 34
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 43
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
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
% 0.13/0.38  # Current number of processed clauses  : 25
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 20
% 0.13/0.38  # ...number of literals in the above   : 136
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 19
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 323
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 40
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2422
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
