%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  85 expanded)
%              Number of clauses        :   23 (  34 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 216 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t200_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))
           => k5_relat_1(X2,k7_relat_1(X3,X1)) = k5_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(X11,X10) = k7_relat_1(X11,k3_xboole_0(k1_relat_1(X11),X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k1_relat_1(k7_relat_1(X17,X16)) = k3_xboole_0(k1_relat_1(X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))
             => k5_relat_1(X2,k7_relat_1(X3,X1)) = k5_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t200_relat_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k5_relat_1(k5_relat_1(X12,X13),X14) = k5_relat_1(X12,k5_relat_1(X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_14,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(X15,k6_relat_1(k2_relat_1(X15))) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_15,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_16,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | k7_relat_1(k7_relat_1(X9,X7),X8) = k7_relat_1(X9,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,k1_relat_1(X19))
      | k1_relat_1(k7_relat_1(X19,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk3_0,esk1_0)))
    & k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)) != k5_relat_1(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k7_relat_1(X21,X20) = k5_relat_1(k6_relat_1(X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_25,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_relat_1(X1,k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),k2_relat_1(esk2_0))) = k2_relat_1(esk2_0)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k7_relat_1(X2,k2_relat_1(X1))) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk1_0),k2_relat_1(esk2_0)) = k7_relat_1(esk3_0,k2_relat_1(esk2_0))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_37,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_38,negated_conjecture,
    ( k5_relat_1(esk2_0,k7_relat_1(esk3_0,k2_relat_1(esk2_0))) = k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)) != k5_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_33]),c_0_36])]),c_0_39])).

cnf(c_0_42,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_23])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.027 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.47  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.47  fof(t200_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))=>k5_relat_1(X2,k7_relat_1(X3,X1))=k5_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 0.19/0.47  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.47  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.47  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.47  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.47  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.47  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.47  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.47  fof(c_0_10, plain, ![X10, X11]:(~v1_relat_1(X11)|k7_relat_1(X11,X10)=k7_relat_1(X11,k3_xboole_0(k1_relat_1(X11),X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.19/0.47  fof(c_0_11, plain, ![X16, X17]:(~v1_relat_1(X17)|k1_relat_1(k7_relat_1(X17,X16))=k3_xboole_0(k1_relat_1(X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.47  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))=>k5_relat_1(X2,k7_relat_1(X3,X1))=k5_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t200_relat_1])).
% 0.19/0.47  fof(c_0_13, plain, ![X12, X13, X14]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|(~v1_relat_1(X14)|k5_relat_1(k5_relat_1(X12,X13),X14)=k5_relat_1(X12,k5_relat_1(X13,X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.47  fof(c_0_14, plain, ![X15]:(~v1_relat_1(X15)|k5_relat_1(X15,k6_relat_1(k2_relat_1(X15)))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.47  fof(c_0_15, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.47  cnf(c_0_16, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_17, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  fof(c_0_18, plain, ![X7, X8, X9]:(~v1_relat_1(X9)|k7_relat_1(k7_relat_1(X9,X7),X8)=k7_relat_1(X9,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.47  fof(c_0_19, plain, ![X18, X19]:(~v1_relat_1(X19)|(~r1_tarski(X18,k1_relat_1(X19))|k1_relat_1(k7_relat_1(X19,X18))=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.47  fof(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk3_0,esk1_0)))&k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0))!=k5_relat_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.47  cnf(c_0_21, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_22, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  fof(c_0_24, plain, ![X20, X21]:(~v1_relat_1(X21)|k7_relat_1(X21,X20)=k5_relat_1(k6_relat_1(X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.47  cnf(c_0_25, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.47  cnf(c_0_26, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_27, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_29, plain, (k5_relat_1(X1,k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2))=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.47  cnf(c_0_30, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_31, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),k2_relat_1(esk2_0)))=k2_relat_1(esk2_0)|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_34, plain, (k5_relat_1(X1,k7_relat_1(X2,k2_relat_1(X1)))=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk1_0),k2_relat_1(esk2_0))=k7_relat_1(esk3_0,k2_relat_1(esk2_0))|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.19/0.47  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  fof(c_0_37, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, (k5_relat_1(esk2_0,k7_relat_1(esk3_0,k2_relat_1(esk2_0)))=k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0))|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0))!=k5_relat_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_40, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_38]), c_0_33]), c_0_36])]), c_0_39])).
% 0.19/0.47  cnf(c_0_42, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_23])])).
% 0.19/0.47  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 44
% 0.19/0.47  # Proof object clause steps            : 23
% 0.19/0.47  # Proof object formula steps           : 21
% 0.19/0.47  # Proof object conjectures             : 12
% 0.19/0.47  # Proof object clause conjectures      : 9
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 13
% 0.19/0.47  # Proof object initial formulas used   : 10
% 0.19/0.47  # Proof object generating inferences   : 10
% 0.19/0.47  # Proof object simplifying inferences  : 14
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 10
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 13
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 13
% 0.19/0.47  # Processed clauses                    : 774
% 0.19/0.47  # ...of these trivial                  : 10
% 0.19/0.47  # ...subsumed                          : 526
% 0.19/0.47  # ...remaining for further processing  : 238
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 24
% 0.19/0.47  # Backward-rewritten                   : 6
% 0.19/0.47  # Generated clauses                    : 4650
% 0.19/0.47  # ...of the previous two non-trivial   : 4337
% 0.19/0.47  # Contextual simplify-reflections      : 74
% 0.19/0.47  # Paramodulations                      : 4650
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 0
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 195
% 0.19/0.47  #    Positive orientable unit clauses  : 19
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 2
% 0.19/0.47  #    Non-unit-clauses                  : 174
% 0.19/0.47  # Current number of unprocessed clauses: 3583
% 0.19/0.47  # ...number of literals in the above   : 13767
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 43
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 6634
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 4804
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 624
% 0.19/0.47  # Unit Clause-clause subsumption calls : 90
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 46
% 0.19/0.47  # BW rewrite match successes           : 4
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 131627
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.119 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.125 s
% 0.19/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
