%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 101 expanded)
%              Number of clauses        :   31 (  42 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 329 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t214_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t214_relat_1])).

fof(c_0_11,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X24] :
      ( ( r2_hidden(esk2_3(X20,X21,X22),k1_relat_1(X22))
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X20),X22)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X21)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X24,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X24,X20),X22)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))
    & ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X27,X28] :
      ( ( k9_relat_1(X28,X27) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_xboole_0(k1_relat_1(X28),X27)
        | k9_relat_1(X28,X27) = k1_xboole_0
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X15,X17)
      | ~ r1_xboole_0(X16,X17)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

fof(c_0_26,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | r1_tarski(k1_relat_1(k3_xboole_0(X25,X26)),k3_xboole_0(k1_relat_1(X25),k1_relat_1(X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ r1_xboole_0(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24]),c_0_23])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_34,plain,
    ( k1_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X3,k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

fof(c_0_39,plain,(
    ! [X29] :
      ( ( k1_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) )
      & ( k2_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_41]),c_0_24])])).

fof(c_0_44,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | v1_relat_1(k3_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.027 s
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t214_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.20/0.43  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.43  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.43  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.20/0.43  fof(t14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 0.20/0.43  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.43  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.43  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.43  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t214_relat_1])).
% 0.20/0.43  fof(c_0_11, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X20, X21, X22, X24]:((((r2_hidden(esk2_3(X20,X21,X22),k1_relat_1(X22))|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X20),X22)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(r2_hidden(esk2_3(X20,X21,X22),X21)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(~r2_hidden(X24,k1_relat_1(X22))|~r2_hidden(k4_tarski(X24,X20),X22)|~r2_hidden(X24,X21)|r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.43  fof(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))&~r1_xboole_0(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.43  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  fof(c_0_17, plain, ![X27, X28]:((k9_relat_1(X28,X27)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_xboole_0(k1_relat_1(X28),X27)|k9_relat_1(X28,X27)=k1_xboole_0|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.20/0.43  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_20, plain, (~v1_relat_1(X1)|~r2_hidden(esk2_3(X2,X3,X1),X4)|~r2_hidden(X2,k9_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.43  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_22, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_23, negated_conjecture, (r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  fof(c_0_25, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X15,X17)|~r1_xboole_0(X16,X17)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.20/0.43  fof(c_0_26, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|r1_tarski(k1_relat_1(k3_xboole_0(X25,X26)),k3_xboole_0(k1_relat_1(X25),k1_relat_1(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).
% 0.20/0.43  cnf(c_0_27, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~r1_xboole_0(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.43  cnf(c_0_29, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24]), c_0_23])])).
% 0.20/0.43  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_33, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.43  cnf(c_0_34, plain, (k1_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),X3)|~r1_xboole_0(X3,k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.43  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (k1_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.43  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.20/0.43  fof(c_0_39, plain, ![X29]:((k1_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))&(k2_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (k1_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_42, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (k1_relat_1(k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_41]), c_0_24])])).
% 0.20/0.43  fof(c_0_44, plain, ![X18, X19]:(~v1_relat_1(X18)|v1_relat_1(k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0|~v1_relat_1(k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.43  cnf(c_0_46, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24])])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_49]), c_0_50]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 52
% 0.20/0.43  # Proof object clause steps            : 31
% 0.20/0.43  # Proof object formula steps           : 21
% 0.20/0.43  # Proof object conjectures             : 18
% 0.20/0.43  # Proof object clause conjectures      : 15
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 16
% 0.20/0.43  # Proof object initial formulas used   : 10
% 0.20/0.43  # Proof object generating inferences   : 15
% 0.20/0.43  # Proof object simplifying inferences  : 11
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 13
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 24
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 24
% 0.20/0.43  # Processed clauses                    : 841
% 0.20/0.43  # ...of these trivial                  : 5
% 0.20/0.43  # ...subsumed                          : 566
% 0.20/0.43  # ...remaining for further processing  : 270
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 17
% 0.20/0.43  # Backward-rewritten                   : 30
% 0.20/0.43  # Generated clauses                    : 2672
% 0.20/0.43  # ...of the previous two non-trivial   : 2380
% 0.20/0.43  # Contextual simplify-reflections      : 1
% 0.20/0.43  # Paramodulations                      : 2672
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 223
% 0.20/0.43  #    Positive orientable unit clauses  : 15
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 205
% 0.20/0.43  # Current number of unprocessed clauses: 1536
% 0.20/0.43  # ...number of literals in the above   : 7407
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 47
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 8215
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 3869
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 399
% 0.20/0.43  # Unit Clause-clause subsumption calls : 231
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 17
% 0.20/0.43  # BW rewrite match successes           : 17
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 47988
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.089 s
% 0.20/0.43  # System time              : 0.004 s
% 0.20/0.43  # Total time               : 0.093 s
% 0.20/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
