%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:17 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 197 expanded)
%              Number of clauses        :   34 (  86 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 374 expanded)
%              Number of equality atoms :   13 (  92 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k4_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,k3_xboole_0(X8,X9))
      | r1_tarski(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_13,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X17)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

fof(c_0_25,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k4_xboole_0(esk4_0,X1),X2),esk2_2(k4_xboole_0(esk4_0,X1),X2)),k4_xboole_0(esk4_0,X1))
    | r1_tarski(k4_xboole_0(esk4_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k4_xboole_0(esk3_0,X1),X2),esk2_2(k4_xboole_0(esk3_0,X1),X2)),k4_xboole_0(esk3_0,X1))
    | r1_tarski(k4_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X10,X12)
      | r1_tarski(X10,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r1_tarski(k2_relat_1(X26),k2_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,X1),k4_xboole_0(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_24])])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20]),c_0_20])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_41]),c_0_18]),c_0_24])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(esk3_0,esk4_0))),k1_setfam_1(k2_tarski(k2_relat_1(esk3_0),k2_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),k1_setfam_1(k2_tarski(X2,k2_relat_1(esk4_0))))
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))),k1_setfam_1(k2_tarski(k2_relat_1(esk4_0),k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_37]),c_0_37]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_37]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:18:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.76  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.60/0.76  # and selection function SelectDiffNegLit.
% 0.60/0.76  #
% 0.60/0.76  # Preprocessing time       : 0.027 s
% 0.60/0.76  # Presaturation interreduction done
% 0.60/0.76  
% 0.60/0.76  # Proof found!
% 0.60/0.76  # SZS status Theorem
% 0.60/0.76  # SZS output start CNFRefutation
% 0.60/0.76  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 0.60/0.76  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.60/0.76  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.60/0.76  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.60/0.76  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.60/0.76  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.60/0.76  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.60/0.76  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.60/0.76  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.60/0.76  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.60/0.76  fof(c_0_10, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k4_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.60/0.76  fof(c_0_11, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.60/0.76  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(X7,k3_xboole_0(X8,X9))|r1_tarski(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.60/0.76  fof(c_0_13, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.60/0.76  fof(c_0_14, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.60/0.76  fof(c_0_15, plain, ![X17, X18, X19, X20, X21]:((~r1_tarski(X17,X18)|(~r2_hidden(k4_tarski(X19,X20),X17)|r2_hidden(k4_tarski(X19,X20),X18))|~v1_relat_1(X17))&((r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)|r1_tarski(X17,X21)|~v1_relat_1(X17))&(~r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)|r1_tarski(X17,X21)|~v1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.60/0.76  cnf(c_0_16, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.76  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.76  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.76  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.76  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.76  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.76  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.76  cnf(c_0_23, negated_conjecture, (v1_relat_1(k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.60/0.76  cnf(c_0_24, negated_conjecture, (v1_relat_1(k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.60/0.76  fof(c_0_25, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.60/0.76  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.60/0.76  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.60/0.76  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.76  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k4_xboole_0(esk4_0,X1),X2),esk2_2(k4_xboole_0(esk4_0,X1),X2)),k4_xboole_0(esk4_0,X1))|r1_tarski(k4_xboole_0(esk4_0,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.60/0.76  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k4_xboole_0(esk3_0,X1),X2),esk2_2(k4_xboole_0(esk3_0,X1),X2)),k4_xboole_0(esk3_0,X1))|r1_tarski(k4_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.60/0.76  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.60/0.76  fof(c_0_32, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X10,X12)|r1_tarski(X10,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.60/0.76  fof(c_0_33, plain, ![X26, X27]:((r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))&(r1_tarski(k2_relat_1(X26),k2_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.60/0.76  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.76  cnf(c_0_35, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,X1),k4_xboole_0(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23])])).
% 0.60/0.76  cnf(c_0_36, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_30]), c_0_24])])).
% 0.60/0.76  cnf(c_0_37, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20]), c_0_20])).
% 0.60/0.76  cnf(c_0_38, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.76  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.60/0.76  cnf(c_0_40, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.60/0.76  cnf(c_0_41, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.60/0.76  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.60/0.76  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.76  cnf(c_0_44, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_20])).
% 0.60/0.76  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17]), c_0_23])])).
% 0.60/0.76  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_41]), c_0_18]), c_0_24])])).
% 0.60/0.76  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 0.60/0.76  cnf(c_0_48, negated_conjecture, (~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(esk3_0,esk4_0))),k1_setfam_1(k2_tarski(k2_relat_1(esk3_0),k2_relat_1(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_20])).
% 0.60/0.76  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),k1_setfam_1(k2_tarski(X2,k2_relat_1(esk4_0))))|~r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.60/0.76  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.60/0.76  cnf(c_0_51, negated_conjecture, (~r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))),k1_setfam_1(k2_tarski(k2_relat_1(esk4_0),k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_37]), c_0_37]), c_0_27])).
% 0.60/0.76  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_37]), c_0_51]), ['proof']).
% 0.60/0.76  # SZS output end CNFRefutation
% 0.60/0.76  # Proof object total steps             : 53
% 0.60/0.76  # Proof object clause steps            : 34
% 0.60/0.76  # Proof object formula steps           : 19
% 0.60/0.76  # Proof object conjectures             : 21
% 0.60/0.76  # Proof object clause conjectures      : 18
% 0.60/0.76  # Proof object formula conjectures     : 3
% 0.60/0.76  # Proof object initial clauses used    : 12
% 0.60/0.76  # Proof object initial formulas used   : 9
% 0.60/0.76  # Proof object generating inferences   : 16
% 0.60/0.76  # Proof object simplifying inferences  : 22
% 0.60/0.76  # Training examples: 0 positive, 0 negative
% 0.60/0.76  # Parsed axioms                        : 9
% 0.60/0.76  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.76  # Initial clauses                      : 14
% 0.60/0.76  # Removed in clause preprocessing      : 1
% 0.60/0.76  # Initial clauses in saturation        : 13
% 0.60/0.76  # Processed clauses                    : 2162
% 0.60/0.76  # ...of these trivial                  : 518
% 0.60/0.76  # ...subsumed                          : 610
% 0.60/0.76  # ...remaining for further processing  : 1034
% 0.60/0.76  # Other redundant clauses eliminated   : 0
% 0.60/0.76  # Clauses deleted for lack of memory   : 0
% 0.60/0.76  # Backward-subsumed                    : 0
% 0.60/0.76  # Backward-rewritten                   : 16
% 0.60/0.76  # Generated clauses                    : 36509
% 0.60/0.76  # ...of the previous two non-trivial   : 32400
% 0.60/0.76  # Contextual simplify-reflections      : 0
% 0.60/0.76  # Paramodulations                      : 36509
% 0.60/0.76  # Factorizations                       : 0
% 0.60/0.76  # Equation resolutions                 : 0
% 0.60/0.76  # Propositional unsat checks           : 0
% 0.60/0.76  #    Propositional check models        : 0
% 0.60/0.76  #    Propositional check unsatisfiable : 0
% 0.60/0.76  #    Propositional clauses             : 0
% 0.60/0.76  #    Propositional clauses after purity: 0
% 0.60/0.76  #    Propositional unsat core size     : 0
% 0.60/0.76  #    Propositional preprocessing time  : 0.000
% 0.60/0.76  #    Propositional encoding time       : 0.000
% 0.60/0.76  #    Propositional solver time         : 0.000
% 0.60/0.76  #    Success case prop preproc time    : 0.000
% 0.60/0.76  #    Success case prop encoding time   : 0.000
% 0.60/0.76  #    Success case prop solver time     : 0.000
% 0.60/0.76  # Current number of processed clauses  : 1005
% 0.60/0.76  #    Positive orientable unit clauses  : 598
% 0.60/0.76  #    Positive unorientable unit clauses: 5
% 0.60/0.76  #    Negative unit clauses             : 1
% 0.60/0.76  #    Non-unit-clauses                  : 401
% 0.60/0.76  # Current number of unprocessed clauses: 30240
% 0.60/0.76  # ...number of literals in the above   : 33027
% 0.60/0.76  # Current number of archived formulas  : 0
% 0.60/0.76  # Current number of archived clauses   : 30
% 0.60/0.76  # Clause-clause subsumption calls (NU) : 23594
% 0.60/0.76  # Rec. Clause-clause subsumption calls : 23102
% 0.60/0.76  # Non-unit clause-clause subsumptions  : 597
% 0.60/0.76  # Unit Clause-clause subsumption calls : 3282
% 0.60/0.76  # Rewrite failures with RHS unbound    : 0
% 0.60/0.76  # BW rewrite match attempts            : 28606
% 0.60/0.76  # BW rewrite match successes           : 75
% 0.60/0.76  # Condensation attempts                : 0
% 0.60/0.76  # Condensation successes               : 0
% 0.60/0.76  # Termbank termtop insertions          : 1403006
% 0.60/0.76  
% 0.60/0.76  # -------------------------------------------------
% 0.60/0.76  # User time                : 0.399 s
% 0.60/0.76  # System time              : 0.028 s
% 0.60/0.76  # Total time               : 0.427 s
% 0.60/0.76  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
