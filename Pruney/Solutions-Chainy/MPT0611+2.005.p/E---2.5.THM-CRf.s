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
% DateTime   : Thu Dec  3 10:52:39 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
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
fof(t215_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t27_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

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
           => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t215_relat_1])).

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
    ! [X26,X27,X28,X30] :
      ( ( r2_hidden(esk2_3(X26,X27,X28),k2_relat_1(X28))
        | ~ r2_hidden(X26,k10_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(X26,esk2_3(X26,X27,X28)),X28)
        | ~ r2_hidden(X26,k10_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X27)
        | ~ r2_hidden(X26,k10_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(X30,k2_relat_1(X28))
        | ~ r2_hidden(k4_tarski(X26,X30),X28)
        | ~ r2_hidden(X30,X27)
        | r2_hidden(X26,k10_relat_1(X28,X27))
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))
    & ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ( k10_relat_1(X32,X31) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_xboole_0(k2_relat_1(X32),X31)
        | k10_relat_1(X32,X31) = k1_xboole_0
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk3_0)) ),
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
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | r1_tarski(k2_relat_1(k3_xboole_0(X33,X34)),k3_xboole_0(k2_relat_1(X33),k2_relat_1(X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_relat_1])])])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_relat_1(esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))
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
    ( k2_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X3,k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

fof(c_0_39,plain,(
    ! [X35] :
      ( ( k1_relat_1(X35) != k1_xboole_0
        | X35 = k1_xboole_0
        | ~ v1_relat_1(X35) )
      & ( k2_relat_1(X35) != k1_xboole_0
        | X35 = k1_xboole_0
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:46:40 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.11/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.016 s
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(t215_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 0.11/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.11/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.11/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.11/0.37  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.11/0.37  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.11/0.37  fof(t27_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 0.11/0.37  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.11/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.11/0.37  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.11/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t215_relat_1])).
% 0.11/0.37  fof(c_0_11, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.11/0.37  fof(c_0_12, plain, ![X26, X27, X28, X30]:((((r2_hidden(esk2_3(X26,X27,X28),k2_relat_1(X28))|~r2_hidden(X26,k10_relat_1(X28,X27))|~v1_relat_1(X28))&(r2_hidden(k4_tarski(X26,esk2_3(X26,X27,X28)),X28)|~r2_hidden(X26,k10_relat_1(X28,X27))|~v1_relat_1(X28)))&(r2_hidden(esk2_3(X26,X27,X28),X27)|~r2_hidden(X26,k10_relat_1(X28,X27))|~v1_relat_1(X28)))&(~r2_hidden(X30,k2_relat_1(X28))|~r2_hidden(k4_tarski(X26,X30),X28)|~r2_hidden(X30,X27)|r2_hidden(X26,k10_relat_1(X28,X27))|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.11/0.37  fof(c_0_13, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.11/0.37  fof(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))&~r1_xboole_0(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.11/0.37  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.37  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.37  fof(c_0_17, plain, ![X31, X32]:((k10_relat_1(X32,X31)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_xboole_0(k2_relat_1(X32),X31)|k10_relat_1(X32,X31)=k1_xboole_0|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.11/0.37  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_19, negated_conjecture, (r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_20, plain, (~v1_relat_1(X1)|~r2_hidden(esk2_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.11/0.37  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.37  cnf(c_0_22, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.37  cnf(c_0_23, negated_conjecture, (r1_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.37  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  fof(c_0_25, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X15,X17)|~r1_xboole_0(X16,X17)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.11/0.37  fof(c_0_26, plain, ![X33, X34]:(~v1_relat_1(X33)|(~v1_relat_1(X34)|r1_tarski(k2_relat_1(k3_xboole_0(X33,X34)),k3_xboole_0(k2_relat_1(X33),k2_relat_1(X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_relat_1])])])).
% 0.11/0.37  cnf(c_0_27, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.11/0.37  cnf(c_0_28, negated_conjecture, (k10_relat_1(esk4_0,k2_relat_1(esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.11/0.37  cnf(c_0_29, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_30, plain, (r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24]), c_0_23])])).
% 0.11/0.37  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.37  fof(c_0_33, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.11/0.37  cnf(c_0_34, plain, (k2_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),X3)|~r1_xboole_0(X3,k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.11/0.37  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.11/0.37  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.37  cnf(c_0_37, negated_conjecture, (k2_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.11/0.37  cnf(c_0_38, plain, (r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.11/0.37  fof(c_0_39, plain, ![X35]:((k1_relat_1(X35)!=k1_xboole_0|X35=k1_xboole_0|~v1_relat_1(X35))&(k2_relat_1(X35)!=k1_xboole_0|X35=k1_xboole_0|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.11/0.37  cnf(c_0_40, negated_conjecture, (k2_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_42, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.11/0.37  cnf(c_0_43, negated_conjecture, (k2_relat_1(k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_41]), c_0_24])])).
% 0.11/0.37  fof(c_0_44, plain, ![X18, X19]:(~v1_relat_1(X18)|v1_relat_1(k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0|~v1_relat_1(k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.11/0.37  cnf(c_0_46, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.11/0.37  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.37  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24])])).
% 0.11/0.37  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.11/0.37  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_49]), c_0_50]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 52
% 0.11/0.37  # Proof object clause steps            : 31
% 0.11/0.37  # Proof object formula steps           : 21
% 0.11/0.37  # Proof object conjectures             : 18
% 0.11/0.37  # Proof object clause conjectures      : 15
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 16
% 0.11/0.37  # Proof object initial formulas used   : 10
% 0.11/0.37  # Proof object generating inferences   : 15
% 0.11/0.37  # Proof object simplifying inferences  : 11
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 13
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 24
% 0.11/0.37  # Removed in clause preprocessing      : 0
% 0.11/0.37  # Initial clauses in saturation        : 24
% 0.11/0.37  # Processed clauses                    : 838
% 0.11/0.37  # ...of these trivial                  : 5
% 0.11/0.37  # ...subsumed                          : 564
% 0.11/0.37  # ...remaining for further processing  : 269
% 0.11/0.37  # Other redundant clauses eliminated   : 0
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 17
% 0.11/0.37  # Backward-rewritten                   : 30
% 0.11/0.37  # Generated clauses                    : 2586
% 0.11/0.37  # ...of the previous two non-trivial   : 2302
% 0.11/0.37  # Contextual simplify-reflections      : 1
% 0.11/0.37  # Paramodulations                      : 2586
% 0.11/0.37  # Factorizations                       : 0
% 0.11/0.37  # Equation resolutions                 : 0
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 222
% 0.11/0.37  #    Positive orientable unit clauses  : 14
% 0.11/0.37  #    Positive unorientable unit clauses: 0
% 0.11/0.37  #    Negative unit clauses             : 3
% 0.11/0.37  #    Non-unit-clauses                  : 205
% 0.11/0.37  # Current number of unprocessed clauses: 1459
% 0.11/0.37  # ...number of literals in the above   : 7137
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 47
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 8212
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 3871
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 398
% 0.11/0.37  # Unit Clause-clause subsumption calls : 190
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 17
% 0.11/0.37  # BW rewrite match successes           : 17
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 46409
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.050 s
% 0.11/0.37  # System time              : 0.003 s
% 0.11/0.37  # Total time               : 0.053 s
% 0.11/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
