%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:55 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :   39 (  76 expanded)
%              Number of clauses        :   20 (  30 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 162 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k7_relat_1(X17,X16),k7_relat_1(X18,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

fof(c_0_13,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k7_relat_1(X24,X23),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(k7_relat_1(X15,X13),X14) = k7_relat_1(X15,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k1_relat_1(X21),k1_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(k2_relat_1(X21),k2_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k2_relat_1(k7_relat_1(esk3_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_25,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X4,X6)
      | r1_tarski(X4,k3_xboole_0(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k2_relat_1(k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22]),c_0_28])).

fof(c_0_32,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | r1_tarski(k2_relat_1(k7_relat_1(X26,X25)),k2_relat_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k3_xboole_0(X4,k2_relat_1(k7_relat_1(X1,X3))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_18])])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X3))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 7.70/7.89  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 7.70/7.89  # and selection function SelectCQIPrecWNTNp.
% 7.70/7.89  #
% 7.70/7.89  # Preprocessing time       : 0.027 s
% 7.70/7.89  # Presaturation interreduction done
% 7.70/7.89  
% 7.70/7.89  # Proof found!
% 7.70/7.89  # SZS status Theorem
% 7.70/7.89  # SZS output start CNFRefutation
% 7.70/7.89  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 7.70/7.89  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.70/7.89  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 7.70/7.89  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 7.70/7.89  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.70/7.89  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 7.70/7.89  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 7.70/7.89  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.70/7.89  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 7.70/7.89  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 7.70/7.89  fof(c_0_10, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 7.70/7.89  fof(c_0_11, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 7.70/7.89  fof(c_0_12, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~r1_tarski(X17,X18)|r1_tarski(k7_relat_1(X17,X16),k7_relat_1(X18,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 7.70/7.89  fof(c_0_13, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k7_relat_1(X24,X23),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 7.70/7.89  fof(c_0_14, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 7.70/7.89  fof(c_0_15, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(k7_relat_1(X15,X13),X14)=k7_relat_1(X15,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 7.70/7.89  cnf(c_0_16, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 7.70/7.89  cnf(c_0_17, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.70/7.89  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 7.70/7.89  fof(c_0_19, plain, ![X21, X22]:((r1_tarski(k1_relat_1(X21),k1_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r1_tarski(k2_relat_1(X21),k2_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 7.70/7.89  cnf(c_0_20, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.70/7.89  cnf(c_0_21, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.70/7.89  cnf(c_0_22, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 7.70/7.89  cnf(c_0_23, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.70/7.89  cnf(c_0_24, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k2_relat_1(k7_relat_1(esk3_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 7.70/7.89  fof(c_0_25, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X4,X6)|r1_tarski(X4,k3_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 7.70/7.89  cnf(c_0_26, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.70/7.89  cnf(c_0_27, plain, (r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 7.70/7.89  cnf(c_0_28, plain, (v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 7.70/7.89  cnf(c_0_29, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18])])).
% 7.70/7.89  cnf(c_0_30, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.70/7.89  cnf(c_0_31, plain, (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k2_relat_1(k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22]), c_0_28])).
% 7.70/7.89  fof(c_0_32, plain, ![X25, X26]:(~v1_relat_1(X26)|r1_tarski(k2_relat_1(k7_relat_1(X26,X25)),k2_relat_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 7.70/7.89  cnf(c_0_33, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_18])])).
% 7.70/7.89  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k3_xboole_0(X4,k2_relat_1(k7_relat_1(X1,X3))))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),X4)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 7.70/7.89  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.70/7.89  cnf(c_0_36, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k3_xboole_0(k2_relat_1(k7_relat_1(esk3_0,esk1_0)),k2_relat_1(k7_relat_1(esk3_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_18])])).
% 7.70/7.89  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X3))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_22])).
% 7.70/7.89  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18])]), ['proof']).
% 7.70/7.89  # SZS output end CNFRefutation
% 7.70/7.89  # Proof object total steps             : 39
% 7.70/7.89  # Proof object clause steps            : 20
% 7.70/7.89  # Proof object formula steps           : 19
% 7.70/7.89  # Proof object conjectures             : 10
% 7.70/7.89  # Proof object clause conjectures      : 7
% 7.70/7.89  # Proof object formula conjectures     : 3
% 7.70/7.89  # Proof object initial clauses used    : 10
% 7.70/7.89  # Proof object initial formulas used   : 9
% 7.70/7.89  # Proof object generating inferences   : 10
% 7.70/7.89  # Proof object simplifying inferences  : 14
% 7.70/7.89  # Training examples: 0 positive, 0 negative
% 7.70/7.89  # Parsed axioms                        : 11
% 7.70/7.89  # Removed by relevancy pruning/SinE    : 0
% 7.70/7.89  # Initial clauses                      : 14
% 7.70/7.89  # Removed in clause preprocessing      : 0
% 7.70/7.89  # Initial clauses in saturation        : 14
% 7.70/7.89  # Processed clauses                    : 12484
% 7.70/7.89  # ...of these trivial                  : 0
% 7.70/7.89  # ...subsumed                          : 9934
% 7.70/7.89  # ...remaining for further processing  : 2550
% 7.70/7.89  # Other redundant clauses eliminated   : 0
% 7.70/7.89  # Clauses deleted for lack of memory   : 0
% 7.70/7.89  # Backward-subsumed                    : 4
% 7.70/7.89  # Backward-rewritten                   : 0
% 7.70/7.89  # Generated clauses                    : 1183377
% 7.70/7.89  # ...of the previous two non-trivial   : 1182836
% 7.70/7.89  # Contextual simplify-reflections      : 1064
% 7.70/7.89  # Paramodulations                      : 1183377
% 7.70/7.89  # Factorizations                       : 0
% 7.70/7.89  # Equation resolutions                 : 0
% 7.70/7.89  # Propositional unsat checks           : 0
% 7.70/7.89  #    Propositional check models        : 0
% 7.70/7.89  #    Propositional check unsatisfiable : 0
% 7.70/7.89  #    Propositional clauses             : 0
% 7.70/7.89  #    Propositional clauses after purity: 0
% 7.70/7.89  #    Propositional unsat core size     : 0
% 7.70/7.89  #    Propositional preprocessing time  : 0.000
% 7.70/7.89  #    Propositional encoding time       : 0.000
% 7.70/7.89  #    Propositional solver time         : 0.000
% 7.70/7.89  #    Success case prop preproc time    : 0.000
% 7.70/7.89  #    Success case prop encoding time   : 0.000
% 7.70/7.89  #    Success case prop solver time     : 0.000
% 7.70/7.89  # Current number of processed clauses  : 2532
% 7.70/7.89  #    Positive orientable unit clauses  : 1
% 7.70/7.89  #    Positive unorientable unit clauses: 0
% 7.70/7.89  #    Negative unit clauses             : 12
% 7.70/7.89  #    Non-unit-clauses                  : 2519
% 7.70/7.89  # Current number of unprocessed clauses: 1170336
% 7.70/7.89  # ...number of literals in the above   : 3327814
% 7.70/7.89  # Current number of archived formulas  : 0
% 7.70/7.89  # Current number of archived clauses   : 18
% 7.70/7.89  # Clause-clause subsumption calls (NU) : 2174615
% 7.70/7.89  # Rec. Clause-clause subsumption calls : 2093716
% 7.70/7.89  # Non-unit clause-clause subsumptions  : 10993
% 7.70/7.89  # Unit Clause-clause subsumption calls : 60
% 7.70/7.89  # Rewrite failures with RHS unbound    : 0
% 7.70/7.89  # BW rewrite match attempts            : 0
% 7.70/7.89  # BW rewrite match successes           : 0
% 7.70/7.89  # Condensation attempts                : 0
% 7.70/7.89  # Condensation successes               : 0
% 7.70/7.89  # Termbank termtop insertions          : 26957796
% 7.76/7.94  
% 7.76/7.94  # -------------------------------------------------
% 7.76/7.94  # User time                : 7.106 s
% 7.76/7.94  # System time              : 0.493 s
% 7.76/7.94  # Total time               : 7.599 s
% 7.76/7.94  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
