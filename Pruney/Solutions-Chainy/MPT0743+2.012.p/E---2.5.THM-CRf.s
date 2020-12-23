%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   67 (1033 expanded)
%              Number of clauses        :   42 ( 448 expanded)
%              Number of leaves         :   12 ( 262 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 (2781 expanded)
%              Number of equality atoms :   30 ( 465 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_13,plain,(
    ! [X10] : k1_ordinal1(X10) = k2_xboole_0(X10,k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ( ~ r2_hidden(esk1_0,esk2_0)
      | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,esk2_0)
      | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( ~ r1_ordinal1(X11,X12)
        | r1_tarski(X11,X12)
        | ~ v3_ordinal1(X11)
        | ~ v3_ordinal1(X12) )
      & ( ~ r1_tarski(X11,X12)
        | r1_ordinal1(X11,X12)
        | ~ v3_ordinal1(X11)
        | ~ v3_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X18] :
      ( ~ v3_ordinal1(X18)
      | v3_ordinal1(k1_ordinal1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(X13,k1_ordinal1(X14))
        | r2_hidden(X13,X14)
        | X13 = X14 )
      & ( ~ r2_hidden(X13,X14)
        | r2_hidden(X13,k1_ordinal1(X14)) )
      & ( X13 != X14
        | r2_hidden(X13,k1_ordinal1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ~ v3_ordinal1(X16)
      | ~ v3_ordinal1(X17)
      | r1_ordinal1(X16,X17)
      | r2_hidden(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0)
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_35,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)) = esk2_0
    | r2_hidden(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_20])).

fof(c_0_51,plain,(
    ! [X15] : X15 != k1_ordinal1(X15) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

fof(c_0_52,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0)
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_32])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42])).

cnf(c_0_58,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_31]),c_0_32])])).

cnf(c_0_62,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_32]),c_0_24])]),c_0_57])).

cnf(c_0_63,plain,
    ( X1 != k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_20])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_59])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.13/0.37  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.13/0.37  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.37  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.13/0.37  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.13/0.37  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.13/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.37  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.13/0.37  fof(c_0_13, plain, ![X10]:k1_ordinal1(X10)=k2_xboole_0(X10,k1_tarski(X10)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.37  fof(c_0_14, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_15, negated_conjecture, (v3_ordinal1(esk1_0)&(v3_ordinal1(esk2_0)&((~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))&(r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.37  cnf(c_0_16, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_18, plain, ![X11, X12]:((~r1_ordinal1(X11,X12)|r1_tarski(X11,X12)|(~v3_ordinal1(X11)|~v3_ordinal1(X12)))&(~r1_tarski(X11,X12)|r1_ordinal1(X11,X12)|(~v3_ordinal1(X11)|~v3_ordinal1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_20, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  fof(c_0_21, plain, ![X18]:(~v3_ordinal1(X18)|v3_ordinal1(k1_ordinal1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.13/0.37  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_25, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_26, plain, ![X13, X14]:((~r2_hidden(X13,k1_ordinal1(X14))|(r2_hidden(X13,X14)|X13=X14))&((~r2_hidden(X13,X14)|r2_hidden(X13,k1_ordinal1(X14)))&(X13!=X14|r2_hidden(X13,k1_ordinal1(X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_28, plain, ![X16, X17]:(~v3_ordinal1(X16)|(~v3_ordinal1(X17)|(r1_ordinal1(X16,X17)|r2_hidden(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.37  fof(c_0_29, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)|~v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.13/0.37  cnf(c_0_31, plain, (v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_25, c_0_20])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)), inference(rw,[status(thm)],[c_0_27, c_0_20])).
% 0.13/0.37  cnf(c_0_35, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  fof(c_0_36, plain, ![X3, X4]:(~r2_hidden(X3,X4)|~r2_hidden(X4,X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.13/0.37  fof(c_0_37, plain, ![X19, X20]:(~r2_hidden(X19,X20)|~r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.37  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.13/0.37  cnf(c_0_40, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))|~v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))|~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24])])).
% 0.13/0.37  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_43, plain, (r1_tarski(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.13/0.37  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_45, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))=esk2_0|r2_hidden(esk1_0,esk2_0)|~r1_tarski(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (esk1_0=esk2_0|~v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))|~r2_hidden(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.37  cnf(c_0_48, plain, (X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|~r2_hidden(esk2_0,k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 0.13/0.37  cnf(c_0_50, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_20])).
% 0.13/0.37  fof(c_0_51, plain, ![X15]:X15!=k1_ordinal1(X15), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.13/0.37  fof(c_0_52, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))=esk2_0|r2_hidden(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)|~v3_ordinal1(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_43]), c_0_24])])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (esk1_0=esk2_0|~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_31]), c_0_32])])).
% 0.13/0.37  cnf(c_0_56, plain, (X1=X2|r2_hidden(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_42])).
% 0.13/0.37  cnf(c_0_58, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.37  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.37  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0))=esk2_0|r2_hidden(k2_xboole_0(esk1_0,k2_tarski(esk1_0,esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_31]), c_0_32])])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (esk1_0=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_32]), c_0_24])]), c_0_57])).
% 0.13/0.37  cnf(c_0_63, plain, (X1!=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_58, c_0_20])).
% 0.13/0.37  cnf(c_0_64, plain, (~r2_hidden(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_44, c_0_59])).
% 0.13/0.37  cnf(c_0_65, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_63]), c_0_64]), c_0_65]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 67
% 0.13/0.37  # Proof object clause steps            : 42
% 0.13/0.37  # Proof object formula steps           : 25
% 0.13/0.37  # Proof object conjectures             : 21
% 0.13/0.37  # Proof object clause conjectures      : 18
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 12
% 0.13/0.37  # Proof object generating inferences   : 16
% 0.13/0.37  # Proof object simplifying inferences  : 36
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 12
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 2
% 0.13/0.37  # Initial clauses in saturation        : 18
% 0.13/0.37  # Processed clauses                    : 69
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 6
% 0.13/0.37  # ...remaining for further processing  : 62
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 3
% 0.13/0.37  # Backward-rewritten                   : 14
% 0.13/0.37  # Generated clauses                    : 74
% 0.13/0.37  # ...of the previous two non-trivial   : 65
% 0.13/0.37  # Contextual simplify-reflections      : 3
% 0.13/0.37  # Paramodulations                      : 69
% 0.13/0.37  # Factorizations                       : 2
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 25
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 15
% 0.13/0.37  # Current number of unprocessed clauses: 29
% 0.13/0.37  # ...number of literals in the above   : 114
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 36
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 117
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 98
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.37  # Unit Clause-clause subsumption calls : 22
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2305
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.032 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
