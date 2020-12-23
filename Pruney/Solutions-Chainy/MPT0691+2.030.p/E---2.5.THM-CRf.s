%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:45 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 274 expanded)
%              Number of clauses        :   38 ( 117 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 534 expanded)
%              Number of equality atoms :   31 ( 122 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_13,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_relat_1(X30)) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | r1_tarski(k10_relat_1(X32,X31),k10_relat_1(X32,k2_relat_1(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k7_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_22,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k2_relat_1(k7_relat_1(X29,X28)) = k9_relat_1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_23,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_20])).

fof(c_0_26,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | k10_relat_1(k7_relat_1(X35,X33),X34) = k3_xboole_0(X33,k10_relat_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_27,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) = k10_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1)) = k10_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(X1,k10_relat_1(esk2_0,X2)) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)),X1) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

fof(c_0_39,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k3_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

fof(c_0_41,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X18,X20)
      | r1_tarski(X18,k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_42,plain,(
    ! [X16,X17] : r1_tarski(k3_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_40]),c_0_35]),c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_relat_1(esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(X1,k1_relat_1(esk2_0)) = k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_29])).

fof(c_0_53,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,k1_relat_1(esk2_0))) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(k1_relat_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k10_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_29]),c_0_35]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.18/0.40  # and selection function SelectComplexG.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.027 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.18/0.40  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.18/0.40  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 0.18/0.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.18/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.18/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.18/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.40  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.18/0.40  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.18/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.18/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.18/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.18/0.40  fof(c_0_13, plain, ![X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_relat_1(X30))=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.18/0.40  fof(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.18/0.40  fof(c_0_15, plain, ![X31, X32]:(~v1_relat_1(X32)|r1_tarski(k10_relat_1(X32,X31),k10_relat_1(X32,k2_relat_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.18/0.40  cnf(c_0_16, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.40  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  fof(c_0_18, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.18/0.40  cnf(c_0_19, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_20, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.40  fof(c_0_21, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k7_relat_1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.18/0.40  fof(c_0_22, plain, ![X28, X29]:(~v1_relat_1(X29)|k2_relat_1(k7_relat_1(X29,X28))=k9_relat_1(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.18/0.40  fof(c_0_23, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.40  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.40  cnf(c_0_25, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_17]), c_0_20])).
% 0.18/0.40  fof(c_0_26, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|k10_relat_1(k7_relat_1(X35,X33),X34)=k3_xboole_0(X33,k10_relat_1(X35,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.18/0.40  cnf(c_0_27, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.40  cnf(c_0_28, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  cnf(c_0_30, negated_conjecture, (k3_xboole_0(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))=k10_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.40  cnf(c_0_31, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.40  cnf(c_0_32, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.18/0.40  cnf(c_0_33, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_17])).
% 0.18/0.40  cnf(c_0_34, negated_conjecture, (k3_xboole_0(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1))=k10_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.40  cnf(c_0_35, negated_conjecture, (k3_xboole_0(X1,k10_relat_1(esk2_0,X2))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 0.18/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_32]), c_0_33])).
% 0.18/0.40  cnf(c_0_37, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)),X1)=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.40  cnf(c_0_38, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.18/0.40  fof(c_0_39, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k3_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.18/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))))), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 0.18/0.40  fof(c_0_41, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X18,X20)|r1_tarski(X18,k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.18/0.40  fof(c_0_42, plain, ![X16, X17]:r1_tarski(k3_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.18/0.40  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))=k1_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_40]), c_0_35]), c_0_37])).
% 0.18/0.40  cnf(c_0_46, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.40  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.40  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk1_0,k1_relat_1(esk2_0))=esk1_0), inference(spm,[status(thm)],[c_0_24, c_0_44])).
% 0.18/0.40  cnf(c_0_50, negated_conjecture, (k3_xboole_0(X1,k1_relat_1(esk2_0))=k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,k1_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.18/0.40  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_29])).
% 0.18/0.40  fof(c_0_53, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.40  cnf(c_0_54, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,k1_relat_1(esk2_0)))=esk1_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.40  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(k1_relat_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.40  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.40  cnf(c_0_57, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.18/0.40  cnf(c_0_58, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.18/0.40  cnf(c_0_59, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k10_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_29]), c_0_35]), c_0_37])).
% 0.18/0.40  cnf(c_0_60, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.18/0.40  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 63
% 0.18/0.40  # Proof object clause steps            : 38
% 0.18/0.40  # Proof object formula steps           : 25
% 0.18/0.40  # Proof object conjectures             : 29
% 0.18/0.40  # Proof object clause conjectures      : 26
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 14
% 0.18/0.40  # Proof object initial formulas used   : 12
% 0.18/0.40  # Proof object generating inferences   : 22
% 0.18/0.40  # Proof object simplifying inferences  : 13
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 15
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 19
% 0.18/0.40  # Removed in clause preprocessing      : 0
% 0.18/0.40  # Initial clauses in saturation        : 19
% 0.18/0.40  # Processed clauses                    : 442
% 0.18/0.40  # ...of these trivial                  : 90
% 0.18/0.40  # ...subsumed                          : 162
% 0.18/0.40  # ...remaining for further processing  : 190
% 0.18/0.40  # Other redundant clauses eliminated   : 2
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 0
% 0.18/0.40  # Backward-rewritten                   : 19
% 0.18/0.40  # Generated clauses                    : 2389
% 0.18/0.40  # ...of the previous two non-trivial   : 1627
% 0.18/0.40  # Contextual simplify-reflections      : 0
% 0.18/0.40  # Paramodulations                      : 2387
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 2
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 151
% 0.18/0.40  #    Positive orientable unit clauses  : 89
% 0.18/0.40  #    Positive unorientable unit clauses: 1
% 0.18/0.40  #    Negative unit clauses             : 1
% 0.18/0.40  #    Non-unit-clauses                  : 60
% 0.18/0.40  # Current number of unprocessed clauses: 1165
% 0.18/0.40  # ...number of literals in the above   : 1393
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 37
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 1043
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 1029
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 161
% 0.18/0.40  # Unit Clause-clause subsumption calls : 39
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 62
% 0.18/0.40  # BW rewrite match successes           : 20
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 26454
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.054 s
% 0.18/0.40  # System time              : 0.007 s
% 0.18/0.40  # Total time               : 0.061 s
% 0.18/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
