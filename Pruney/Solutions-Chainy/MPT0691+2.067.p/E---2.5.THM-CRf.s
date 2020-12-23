%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  90 expanded)
%              Number of clauses        :   25 (  36 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 206 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_11,plain,(
    ! [X20] :
      ( ~ v1_relat_1(X20)
      | k10_relat_1(X20,k2_relat_1(X20)) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_12,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,k1_relat_1(X16)) = k2_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_13,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X25,k1_relat_1(X26))
      | k1_relat_1(k7_relat_1(X26,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k1_relat_1(k7_relat_1(X24,X23)) = k3_xboole_0(k1_relat_1(X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_22,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(X18,X19)
      | k9_relat_1(k7_relat_1(X17,X19),X18) = k9_relat_1(X17,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0)) = esk1_0
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | k10_relat_1(k7_relat_1(X29,X27),X28) = k3_xboole_0(X27,k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk1_0,X1) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_35,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk1_0,X1) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_19])])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k1_relat_1(k7_relat_1(X22,X21)),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19])])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(k7_relat_1(X1,esk1_0),X2) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.13/0.39  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.13/0.39  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.39  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.39  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.39  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.13/0.39  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.13/0.39  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.13/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.13/0.39  fof(c_0_11, plain, ![X20]:(~v1_relat_1(X20)|k10_relat_1(X20,k2_relat_1(X20))=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.13/0.39  fof(c_0_12, plain, ![X16]:(~v1_relat_1(X16)|k9_relat_1(X16,k1_relat_1(X16))=k2_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.39  fof(c_0_13, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X25,k1_relat_1(X26))|k1_relat_1(k7_relat_1(X26,X25))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.13/0.39  fof(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.39  cnf(c_0_15, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_16, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_17, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_20, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X23, X24]:(~v1_relat_1(X24)|k1_relat_1(k7_relat_1(X24,X23))=k3_xboole_0(k1_relat_1(X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.39  cnf(c_0_22, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.39  fof(c_0_24, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.39  fof(c_0_25, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~r1_tarski(X18,X19)|k9_relat_1(k7_relat_1(X17,X19),X18)=k9_relat_1(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0))=esk1_0|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.39  cnf(c_0_29, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_30, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.13/0.39  fof(c_0_32, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|k10_relat_1(k7_relat_1(X29,X27),X28)=k3_xboole_0(X27,k10_relat_1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k3_xboole_0(esk1_0,X1)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])])).
% 0.13/0.39  cnf(c_0_35, plain, (k9_relat_1(k7_relat_1(X1,X2),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_36, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k3_xboole_0(esk1_0,X1)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_19])])).
% 0.13/0.39  fof(c_0_38, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k1_relat_1(k7_relat_1(X22,X21)),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19])])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (k10_relat_1(k7_relat_1(X1,esk1_0),X2)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.39  cnf(c_0_41, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_19])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 46
% 0.13/0.39  # Proof object clause steps            : 25
% 0.13/0.39  # Proof object formula steps           : 21
% 0.13/0.39  # Proof object conjectures             : 16
% 0.13/0.39  # Proof object clause conjectures      : 13
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 12
% 0.13/0.39  # Proof object initial formulas used   : 10
% 0.13/0.39  # Proof object generating inferences   : 12
% 0.13/0.39  # Proof object simplifying inferences  : 14
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 17
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 17
% 0.13/0.39  # Processed clauses                    : 250
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 122
% 0.13/0.39  # ...remaining for further processing  : 127
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 14
% 0.13/0.39  # Generated clauses                    : 859
% 0.13/0.39  # ...of the previous two non-trivial   : 749
% 0.13/0.39  # Contextual simplify-reflections      : 6
% 0.13/0.39  # Paramodulations                      : 857
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 2
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 94
% 0.13/0.39  #    Positive orientable unit clauses  : 26
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 66
% 0.13/0.39  # Current number of unprocessed clauses: 531
% 0.13/0.39  # ...number of literals in the above   : 1669
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 31
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 708
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 672
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 129
% 0.13/0.39  # Unit Clause-clause subsumption calls : 17
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 31
% 0.13/0.39  # BW rewrite match successes           : 11
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 16619
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.045 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.049 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
