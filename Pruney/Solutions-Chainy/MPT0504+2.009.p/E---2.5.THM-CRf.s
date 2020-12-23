%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  89 expanded)
%              Number of clauses        :   27 (  41 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 231 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t102_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t102_relat_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k1_relat_1(k7_relat_1(X27,X26)),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X28)
      | k7_relat_1(X29,X28) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k7_relat_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,X2) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),X1)) = k1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,X1),X2) = k7_relat_1(esk5_0,X1)
    | r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,X1)),X2),k1_relat_1(k7_relat_1(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),k1_relat_1(k7_relat_1(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_42]),c_0_29])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.20/0.44  # and selection function SelectDivPreferIntoLits.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.027 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t102_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 0.20/0.44  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.44  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.44  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.44  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.44  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.44  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.44  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,X1)))), inference(assume_negation,[status(cth)],[t102_relat_1])).
% 0.20/0.44  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.44  fof(c_0_10, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.44  fof(c_0_11, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.44  fof(c_0_12, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k1_relat_1(k7_relat_1(X27,X26)),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.44  fof(c_0_13, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k7_relat_1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.44  fof(c_0_14, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X28)|k7_relat_1(X29,X28)=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.44  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.44  fof(c_0_16, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k7_relat_1(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.44  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.44  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.44  cnf(c_0_20, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.44  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_22, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.44  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_24, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.44  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.44  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.20/0.44  cnf(c_0_27, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.44  cnf(c_0_28, plain, (k7_relat_1(X1,X2)=X1|r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.44  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.20/0.44  cnf(c_0_30, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_32, negated_conjecture, (k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),X1))=k1_relat_1(k7_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.44  cnf(c_0_33, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k7_relat_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,X1),X2)=k7_relat_1(esk5_0,X1)|r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,X1)),X2),k1_relat_1(k7_relat_1(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),k1_relat_1(k7_relat_1(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.44  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk5_0,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.44  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_42]), c_0_29])]), c_0_33]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 44
% 0.20/0.44  # Proof object clause steps            : 27
% 0.20/0.44  # Proof object formula steps           : 17
% 0.20/0.44  # Proof object conjectures             : 18
% 0.20/0.44  # Proof object clause conjectures      : 15
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 11
% 0.20/0.44  # Proof object initial formulas used   : 8
% 0.20/0.44  # Proof object generating inferences   : 13
% 0.20/0.44  # Proof object simplifying inferences  : 6
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 8
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 17
% 0.20/0.44  # Removed in clause preprocessing      : 1
% 0.20/0.44  # Initial clauses in saturation        : 16
% 0.20/0.44  # Processed clauses                    : 278
% 0.20/0.44  # ...of these trivial                  : 2
% 0.20/0.44  # ...subsumed                          : 100
% 0.20/0.44  # ...remaining for further processing  : 176
% 0.20/0.44  # Other redundant clauses eliminated   : 35
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 0
% 0.20/0.44  # Backward-rewritten                   : 1
% 0.20/0.44  # Generated clauses                    : 3721
% 0.20/0.44  # ...of the previous two non-trivial   : 3164
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 3684
% 0.20/0.44  # Factorizations                       : 2
% 0.20/0.44  # Equation resolutions                 : 35
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 156
% 0.20/0.44  #    Positive orientable unit clauses  : 32
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 1
% 0.20/0.44  #    Non-unit-clauses                  : 123
% 0.20/0.44  # Current number of unprocessed clauses: 2913
% 0.20/0.44  # ...number of literals in the above   : 13794
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 18
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 3150
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 1364
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 98
% 0.20/0.44  # Unit Clause-clause subsumption calls : 134
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 89
% 0.20/0.44  # BW rewrite match successes           : 1
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 73618
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.089 s
% 0.20/0.44  # System time              : 0.007 s
% 0.20/0.44  # Total time               : 0.097 s
% 0.20/0.44  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
