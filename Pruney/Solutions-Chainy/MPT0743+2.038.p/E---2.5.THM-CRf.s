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
% DateTime   : Thu Dec  3 10:56:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   67 (1133 expanded)
%              Number of clauses        :   46 ( 479 expanded)
%              Number of leaves         :   10 ( 282 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (3744 expanded)
%              Number of equality atoms :   36 ( 372 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

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

fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ( ~ r1_ordinal1(X8,X9)
        | r1_tarski(X8,X9)
        | ~ v3_ordinal1(X8)
        | ~ v3_ordinal1(X9) )
      & ( ~ r1_tarski(X8,X9)
        | r1_ordinal1(X8,X9)
        | ~ v3_ordinal1(X8)
        | ~ v3_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ~ v3_ordinal1(X13)
      | ~ v3_ordinal1(X14)
      | r1_ordinal1(X13,X14)
      | r2_hidden(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_12,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( ~ r2_hidden(X10,k1_ordinal1(X11))
        | r2_hidden(X10,X11)
        | X10 = X11 )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,k1_ordinal1(X11)) )
      & ( X10 != X11
        | r2_hidden(X10,k1_ordinal1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_17,plain,(
    ! [X7] : k1_ordinal1(X7) = k2_xboole_0(X7,k1_tarski(X7)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ( ~ r2_hidden(esk1_0,esk2_0)
      | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,esk2_0)
      | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X15] :
      ( ~ v3_ordinal1(X15)
      | v3_ordinal1(k1_ordinal1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_tarski(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_29]),c_0_30])])).

cnf(c_0_35,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_tarski(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 = esk2_0
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30]),c_0_36])])).

fof(c_0_42,plain,(
    ! [X5,X6] :
      ( ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(X6)
      | r1_ordinal1(X5,X6)
      | r1_ordinal1(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_tarski(esk1_0)) = esk2_0
    | r2_hidden(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_tarski(esk1_0)) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0)
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_19]),c_0_30])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( esk1_0 = esk2_0
    | r2_hidden(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_30])])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_50,plain,
    ( r1_ordinal1(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_tarski(esk1_0)) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_36])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( esk1_0 = esk2_0
    | r2_hidden(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_36])])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 = esk2_0
    | r1_ordinal1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_36]),c_0_30])])).

fof(c_0_55,plain,(
    ! [X12] : X12 != k1_ordinal1(X12) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_tarski(esk1_0)) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 = esk2_0
    | r2_hidden(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk1_0 = esk2_0
    | r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_54]),c_0_30]),c_0_36])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_tarski(esk1_0)) = esk2_0
    | r2_hidden(esk1_0,esk2_0)
    | ~ r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( X1 != k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_65]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.12/0.37  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.12/0.37  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.12/0.37  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.12/0.37  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.12/0.37  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.12/0.37  fof(c_0_10, plain, ![X8, X9]:((~r1_ordinal1(X8,X9)|r1_tarski(X8,X9)|(~v3_ordinal1(X8)|~v3_ordinal1(X9)))&(~r1_tarski(X8,X9)|r1_ordinal1(X8,X9)|(~v3_ordinal1(X8)|~v3_ordinal1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X13, X14]:(~v3_ordinal1(X13)|(~v3_ordinal1(X14)|(r1_ordinal1(X13,X14)|r2_hidden(X14,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.12/0.37  fof(c_0_16, plain, ![X10, X11]:((~r2_hidden(X10,k1_ordinal1(X11))|(r2_hidden(X10,X11)|X10=X11))&((~r2_hidden(X10,X11)|r2_hidden(X10,k1_ordinal1(X11)))&(X10!=X11|r2_hidden(X10,k1_ordinal1(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X7]:k1_ordinal1(X7)=k2_xboole_0(X7,k1_tarski(X7)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.12/0.37  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  fof(c_0_20, negated_conjecture, (v3_ordinal1(esk1_0)&(v3_ordinal1(esk2_0)&((~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))&(r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_23, plain, (X1=X2|r2_hidden(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_25, plain, ![X15]:(~v3_ordinal1(X15)|v3_ordinal1(k1_ordinal1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.12/0.37  fof(c_0_26, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_28, plain, (X1=X2|r2_hidden(X2,X1)|r2_hidden(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_31, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_33, plain, (X1=X2|r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_tarski(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)|~v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_29]), c_0_30])])).
% 0.12/0.37  cnf(c_0_35, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_31, c_0_22])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_38, plain, (X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_tarski(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)), inference(rw,[status(thm)],[c_0_37, c_0_22])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (esk1_0=esk2_0|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_30]), c_0_36])])).
% 0.12/0.37  fof(c_0_42, plain, ![X5, X6]:(~v3_ordinal1(X5)|~v3_ordinal1(X6)|(r1_ordinal1(X5,X6)|r1_ordinal1(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (k2_xboole_0(esk1_0,k1_tarski(esk1_0))=esk2_0|r2_hidden(esk1_0,esk2_0)|~r1_tarski(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(spm,[status(thm)],[c_0_18, c_0_39])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (esk1_0=esk2_0|~r1_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.37  cnf(c_0_45, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk1_0,k1_tarski(esk1_0))=esk2_0|r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)|~v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_19]), c_0_30])])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (esk1_0=esk2_0|r2_hidden(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0)))|~v3_ordinal1(k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_14]), c_0_30])])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (esk1_0=esk2_0|~r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.12/0.37  cnf(c_0_50, plain, (r1_ordinal1(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_13, c_0_45])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (k2_xboole_0(esk1_0,k1_tarski(esk1_0))=esk2_0|r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_36])])).
% 0.12/0.37  cnf(c_0_52, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_47, c_0_22])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (esk1_0=esk2_0|r2_hidden(esk2_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_36])])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (esk1_0=esk2_0|r1_ordinal1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_36]), c_0_30])])).
% 0.12/0.37  fof(c_0_55, plain, ![X12]:X12!=k1_ordinal1(X12), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (k2_xboole_0(esk1_0,k1_tarski(esk1_0))=esk2_0|r2_hidden(k2_xboole_0(esk1_0,k1_tarski(esk1_0)),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_51])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (esk1_0=esk2_0|r2_hidden(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (esk1_0=esk2_0|r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_54]), c_0_30]), c_0_36])])).
% 0.12/0.37  cnf(c_0_59, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_60, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk1_0,k1_tarski(esk1_0))=esk2_0|r2_hidden(esk1_0,esk2_0)|~r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),k2_xboole_0(esk1_0,k1_tarski(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_56])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (esk1_0=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_57]), c_0_58])).
% 0.12/0.37  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_59])).
% 0.12/0.37  cnf(c_0_64, plain, (X1!=k2_xboole_0(X1,k1_tarski(X1))), inference(rw,[status(thm)],[c_0_60, c_0_22])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_63])]), c_0_64])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_65]), c_0_63])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 67
% 0.12/0.37  # Proof object clause steps            : 46
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 27
% 0.12/0.37  # Proof object clause conjectures      : 24
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 23
% 0.12/0.37  # Proof object simplifying inferences  : 39
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 102
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 33
% 0.12/0.37  # ...remaining for further processing  : 68
% 0.12/0.37  # Other redundant clauses eliminated   : 3
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 11
% 0.12/0.37  # Backward-rewritten                   : 22
% 0.12/0.37  # Generated clauses                    : 131
% 0.12/0.37  # ...of the previous two non-trivial   : 123
% 0.12/0.37  # Contextual simplify-reflections      : 5
% 0.12/0.37  # Paramodulations                      : 124
% 0.12/0.37  # Factorizations                       : 4
% 0.12/0.37  # Equation resolutions                 : 3
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 32
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 21
% 0.12/0.37  # Current number of unprocessed clauses: 38
% 0.12/0.37  # ...number of literals in the above   : 135
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 34
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 267
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 193
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 48
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3068
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
