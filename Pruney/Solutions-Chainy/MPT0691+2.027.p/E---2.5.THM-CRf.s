%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 206 expanded)
%              Number of clauses        :   36 (  92 expanded)
%              Number of leaves         :   12 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 440 expanded)
%              Number of equality atoms :   34 ( 122 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,k3_xboole_0(X17,X18))
      | r1_tarski(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_13,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k10_relat_1(X29,X28),k1_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k2_relat_1(k7_relat_1(X24,X23)) = k9_relat_1(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_21,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k7_relat_1(X35,k1_relat_1(X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1)) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | k10_relat_1(k7_relat_1(X38,X36),X37) = k3_xboole_0(X36,k10_relat_1(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k7_relat_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_26,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_relat_1(X30)) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_27,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k9_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,k10_relat_1(X2,X4))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | r1_tarski(k1_relat_1(k7_relat_1(X34,X33)),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_xboole_0(k1_relat_1(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_39]),c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0) = k9_relat_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_44])])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_53]),c_0_54])).

cnf(c_0_57,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_44])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:55:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.45  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.027 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.20/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.45  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.20/0.45  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.45  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.45  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.45  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.45  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.45  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.45  fof(c_0_12, plain, ![X16, X17, X18]:(~r1_tarski(X16,k3_xboole_0(X17,X18))|r1_tarski(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.20/0.45  fof(c_0_13, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.45  fof(c_0_14, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.45  fof(c_0_15, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k10_relat_1(X29,X28),k1_relat_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.20/0.45  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_19, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  fof(c_0_20, plain, ![X23, X24]:(~v1_relat_1(X24)|k2_relat_1(k7_relat_1(X24,X23))=k9_relat_1(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.45  fof(c_0_21, plain, ![X35]:(~v1_relat_1(X35)|k7_relat_1(X35,k1_relat_1(X35))=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.45  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.45  cnf(c_0_23, plain, (k3_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.45  fof(c_0_24, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|k10_relat_1(k7_relat_1(X38,X36),X37)=k3_xboole_0(X36,k10_relat_1(X38,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.45  fof(c_0_25, plain, ![X21, X22]:(~v1_relat_1(X21)|v1_relat_1(k7_relat_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.45  fof(c_0_26, plain, ![X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_relat_1(X30))=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.45  cnf(c_0_27, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_28, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_29, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.45  cnf(c_0_30, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_31, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_32, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_33, plain, (k2_relat_1(X1)=k9_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.45  fof(c_0_34, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.20/0.45  cnf(c_0_35, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)|~r1_tarski(X1,k3_xboole_0(X3,k10_relat_1(X2,X4)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.45  cnf(c_0_36, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.45  fof(c_0_37, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.20/0.45  cnf(c_0_38, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)|~r1_tarski(X1,k3_xboole_0(X3,k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  fof(c_0_40, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  fof(c_0_41, plain, ![X33, X34]:(~v1_relat_1(X34)|r1_tarski(k1_relat_1(k7_relat_1(X34,X33)),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.45  cnf(c_0_42, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)|~r1_tarski(X1,k3_xboole_0(k1_relat_1(X2),X3))), inference(spm,[status(thm)],[c_0_38, c_0_17])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k1_relat_1(esk2_0),esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_39]), c_0_17])).
% 0.20/0.45  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_47, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.45  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.45  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_50, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.45  cnf(c_0_52, plain, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_33]), c_0_31])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_44])])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0)=k9_relat_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_44])])).
% 0.20/0.45  cnf(c_0_55, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_22, c_0_49])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_53]), c_0_54])).
% 0.20/0.45  cnf(c_0_57, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_30])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_44])])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_44])]), c_0_59]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 61
% 0.20/0.45  # Proof object clause steps            : 36
% 0.20/0.45  # Proof object formula steps           : 25
% 0.20/0.45  # Proof object conjectures             : 14
% 0.20/0.45  # Proof object clause conjectures      : 11
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 15
% 0.20/0.45  # Proof object initial formulas used   : 12
% 0.20/0.45  # Proof object generating inferences   : 20
% 0.20/0.45  # Proof object simplifying inferences  : 16
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 17
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 21
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 21
% 0.20/0.45  # Processed clauses                    : 1085
% 0.20/0.45  # ...of these trivial                  : 136
% 0.20/0.45  # ...subsumed                          : 652
% 0.20/0.45  # ...remaining for further processing  : 297
% 0.20/0.45  # Other redundant clauses eliminated   : 2
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 3
% 0.20/0.45  # Backward-rewritten                   : 4
% 0.20/0.45  # Generated clauses                    : 5325
% 0.20/0.45  # ...of the previous two non-trivial   : 4386
% 0.20/0.45  # Contextual simplify-reflections      : 13
% 0.20/0.45  # Paramodulations                      : 5323
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 2
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 268
% 0.20/0.45  #    Positive orientable unit clauses  : 75
% 0.20/0.45  #    Positive unorientable unit clauses: 1
% 0.20/0.45  #    Negative unit clauses             : 1
% 0.20/0.45  #    Non-unit-clauses                  : 191
% 0.20/0.45  # Current number of unprocessed clauses: 3302
% 0.20/0.45  # ...number of literals in the above   : 8154
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 27
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 4757
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 4356
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 668
% 0.20/0.45  # Unit Clause-clause subsumption calls : 16
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 54
% 0.20/0.45  # BW rewrite match successes           : 7
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 60508
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.105 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.112 s
% 0.20/0.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
