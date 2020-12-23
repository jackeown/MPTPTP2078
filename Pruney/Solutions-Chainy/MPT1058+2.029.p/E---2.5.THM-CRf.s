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
% DateTime   : Thu Dec  3 11:07:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 257 expanded)
%              Number of clauses        :   38 ( 107 expanded)
%              Number of leaves         :   13 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 547 expanded)
%              Number of equality atoms :   40 ( 174 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(c_0_13,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k10_relat_1(X15,k2_relat_1(X15)) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_14,plain,(
    ! [X19] :
      ( k1_relat_1(k6_relat_1(X19)) = X19
      & k2_relat_1(k6_relat_1(X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_15,plain,(
    ! [X20] :
      ( v1_relat_1(k6_relat_1(X20))
      & v1_funct_1(k6_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k10_relat_1(X18,X16),k10_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_17,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k10_relat_1(X12,X11),k1_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])])).

cnf(c_0_28,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_30,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_34,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | k9_relat_1(X10,k1_relat_1(X10)) = k2_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(k6_relat_1(X1),esk2_0) = X1
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_28])])).

cnf(c_0_40,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_18]),c_0_20])])).

cnf(c_0_41,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_20])])).

fof(c_0_44,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k10_relat_1(X14,X13) = k10_relat_1(X14,k3_xboole_0(k2_relat_1(X14),X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_45,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X1
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_20]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(k6_relat_1(X1),esk2_0) = X1
    | ~ r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_51,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_52,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_53,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(k7_relat_1(X23,X21),X22) = k3_xboole_0(X21,k10_relat_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_50])])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k3_xboole_0(esk2_0,k10_relat_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_40]),c_0_18]),c_0_41]),c_0_20])]),c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk2_0,k10_relat_1(esk1_0,esk3_0)) != k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_61]),c_0_62])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.13/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.39  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.13/0.39  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 0.13/0.39  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.39  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.13/0.39  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.39  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.13/0.39  fof(c_0_13, plain, ![X15]:(~v1_relat_1(X15)|k10_relat_1(X15,k2_relat_1(X15))=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.13/0.39  fof(c_0_14, plain, ![X19]:(k1_relat_1(k6_relat_1(X19))=X19&k2_relat_1(k6_relat_1(X19))=X19), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.39  fof(c_0_15, plain, ![X20]:(v1_relat_1(k6_relat_1(X20))&v1_funct_1(k6_relat_1(X20))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.39  fof(c_0_16, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(X16,X17)|r1_tarski(k10_relat_1(X18,X16),k10_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.13/0.39  cnf(c_0_17, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_18, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_19, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_21, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k10_relat_1(X12,X11),k1_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.13/0.39  fof(c_0_22, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_23, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_24, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.39  cnf(c_0_25, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_27, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20])])).
% 0.13/0.39  cnf(c_0_28, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_20])])).
% 0.13/0.39  fof(c_0_29, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.13/0.39  cnf(c_0_30, plain, (k10_relat_1(k6_relat_1(X1),X2)=X1|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.39  fof(c_0_31, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.13/0.39  cnf(c_0_32, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_20])])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  fof(c_0_34, plain, ![X10]:(~v1_relat_1(X10)|k9_relat_1(X10,k1_relat_1(X10))=k2_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.39  fof(c_0_35, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),esk2_0))|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_37, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (k10_relat_1(k6_relat_1(X1),esk2_0)=X1|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_36]), c_0_28])])).
% 0.13/0.39  cnf(c_0_40, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_18]), c_0_20])])).
% 0.13/0.39  cnf(c_0_41, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_42, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_20])])).
% 0.13/0.39  fof(c_0_44, plain, ![X13, X14]:(~v1_relat_1(X14)|k10_relat_1(X14,X13)=k10_relat_1(X14,k3_xboole_0(k2_relat_1(X14),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.13/0.39  cnf(c_0_45, plain, (k10_relat_1(k6_relat_1(X1),X2)=X1|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_30]), c_0_20]), c_0_28])])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_28])).
% 0.13/0.39  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_48, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k10_relat_1(k6_relat_1(X1),esk2_0)=X1|~r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.13/0.39  fof(c_0_51, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  fof(c_0_52, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.39  fof(c_0_53, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|k10_relat_1(k7_relat_1(X23,X21),X22)=k3_xboole_0(X21,k10_relat_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),k3_xboole_0(k2_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_48])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_50])])).
% 0.13/0.39  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_59, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k3_xboole_0(esk2_0,k10_relat_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_40]), c_0_18]), c_0_41]), c_0_20])]), c_0_56])).
% 0.13/0.39  cnf(c_0_62, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk2_0,k10_relat_1(esk1_0,esk3_0))!=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_61]), c_0_62])]), c_0_63]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 65
% 0.13/0.39  # Proof object clause steps            : 38
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 15
% 0.13/0.39  # Proof object clause conjectures      : 12
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 18
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 19
% 0.13/0.39  # Proof object simplifying inferences  : 37
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 227
% 0.13/0.39  # ...of these trivial                  : 8
% 0.13/0.39  # ...subsumed                          : 95
% 0.13/0.39  # ...remaining for further processing  : 124
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 795
% 0.13/0.39  # ...of the previous two non-trivial   : 644
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 793
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
% 0.13/0.39  # Current number of processed clauses  : 100
% 0.13/0.39  #    Positive orientable unit clauses  : 21
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 75
% 0.13/0.39  # Current number of unprocessed clauses: 454
% 0.13/0.39  # ...number of literals in the above   : 1431
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 22
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 833
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 753
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 94
% 0.13/0.39  # Unit Clause-clause subsumption calls : 43
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 40
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 12555
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.044 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
