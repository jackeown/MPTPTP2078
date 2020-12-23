%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (1625 expanded)
%              Number of clauses        :   42 ( 686 expanded)
%              Number of leaves         :   11 ( 469 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 (2743 expanded)
%              Number of equality atoms :   67 (1839 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) )
      & ( X19 != X21
        | ~ r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) )
      & ( ~ r2_hidden(X19,X20)
        | X19 = X21
        | r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_15,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(k1_tarski(X17),k1_tarski(X18)) != k1_tarski(X17)
        | X17 != X18 )
      & ( X17 = X18
        | k4_xboole_0(k1_tarski(X17),k1_tarski(X18)) = k1_tarski(X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X4,X5] :
      ( ( ~ r2_hidden(esk1_2(X4,X5),X4)
        | ~ r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 )
      & ( r2_hidden(esk1_2(X4,X5),X4)
        | r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_31,plain,
    ( X1 != X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

fof(c_0_32,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ r1_tarski(X25,X27)
      | r1_tarski(k1_setfam_1(X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_29])])).

fof(c_0_41,plain,(
    ! [X22,X23] :
      ( ( r2_hidden(esk2_2(X22,X23),X22)
        | X22 = k1_xboole_0
        | r1_tarski(X23,k1_setfam_1(X22)) )
      & ( ~ r1_tarski(X23,esk2_2(X22,X23))
        | X22 = k1_xboole_0
        | r1_tarski(X23,k1_setfam_1(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_43,plain,
    ( esk1_2(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(k1_setfam_1(X3),X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_40]),c_0_34])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk2_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( esk2_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_44]),c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1))),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_40])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2))),k1_setfam_1(X1))
    | ~ r2_hidden(esk2_2(X1,k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2)))),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_49])).

cnf(c_0_53,plain,
    ( X1 = k1_setfam_1(k2_enumset1(X2,X2,X2,X2))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X2)),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1))),k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_44])).

fof(c_0_55,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1))) = k1_setfam_1(X1)
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])])).

cnf(c_0_57,plain,
    ( X1 = k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2)))
    | ~ r1_tarski(X1,k1_setfam_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

fof(c_0_58,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | ~ r1_tarski(X1,k1_setfam_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_29])]),c_0_40])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.13/0.40  # and selection function SelectComplexExceptRRHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.13/0.40  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.13/0.40  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.13/0.40  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.13/0.40  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.13/0.40  fof(c_0_11, plain, ![X19, X20, X21]:(((r2_hidden(X19,X20)|~r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))))&(X19!=X21|~r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21)))))&(~r2_hidden(X19,X20)|X19=X21|r2_hidden(X19,k4_xboole_0(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.13/0.40  fof(c_0_12, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  fof(c_0_13, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_14, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  cnf(c_0_15, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_19, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.40  fof(c_0_20, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.40  fof(c_0_21, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X17, X18]:((k4_xboole_0(k1_tarski(X17),k1_tarski(X18))!=k1_tarski(X17)|X17!=X18)&(X17=X18|k4_xboole_0(k1_tarski(X17),k1_tarski(X18))=k1_tarski(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.13/0.40  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_26, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_27, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_28, plain, (~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.40  fof(c_0_30, plain, ![X4, X5]:((~r2_hidden(esk1_2(X4,X5),X4)|~r2_hidden(esk1_2(X4,X5),X5)|X4=X5)&(r2_hidden(esk1_2(X4,X5),X4)|r2_hidden(esk1_2(X4,X5),X5)|X4=X5)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.13/0.40  cnf(c_0_31, plain, (X1!=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.13/0.40  fof(c_0_32, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~r1_tarski(X25,X27)|r1_tarski(k1_setfam_1(X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 0.13/0.40  cnf(c_0_33, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.13/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_36, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.20/0.40  cnf(c_0_39, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_29])])).
% 0.20/0.40  fof(c_0_41, plain, ![X22, X23]:((r2_hidden(esk2_2(X22,X23),X22)|(X22=k1_xboole_0|r1_tarski(X23,k1_setfam_1(X22))))&(~r1_tarski(X23,esk2_2(X22,X23))|(X22=k1_xboole_0|r1_tarski(X23,k1_setfam_1(X22))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.40  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 0.20/0.40  cnf(c_0_43, plain, (esk1_2(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.40  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(k1_setfam_1(X3),X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_37, c_0_42])).
% 0.20/0.40  cnf(c_0_46, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_43]), c_0_40]), c_0_34])).
% 0.20/0.40  cnf(c_0_47, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk2_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_48, plain, (esk2_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_44]), c_0_40])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1))),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_51, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_40])).
% 0.20/0.40  cnf(c_0_52, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2))),k1_setfam_1(X1))|~r2_hidden(esk2_2(X1,k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2)))),X2)), inference(spm,[status(thm)],[c_0_47, c_0_49])).
% 0.20/0.40  cnf(c_0_53, plain, (X1=k1_setfam_1(k2_enumset1(X2,X2,X2,X2))|~r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X2)),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1))),k1_setfam_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_44])).
% 0.20/0.40  fof(c_0_55, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.20/0.40  cnf(c_0_56, plain, (k1_setfam_1(k2_enumset1(k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1),k1_setfam_1(X1)))=k1_setfam_1(X1)|X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])])).
% 0.20/0.40  cnf(c_0_57, plain, (X1=k1_setfam_1(k2_enumset1(k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2),k1_setfam_1(X2)))|~r1_tarski(X1,k1_setfam_1(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 0.20/0.40  fof(c_0_58, negated_conjecture, k1_setfam_1(k1_tarski(esk3_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).
% 0.20/0.40  cnf(c_0_59, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1|~r1_tarski(X1,k1_setfam_1(X2))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k1_setfam_1(k1_tarski(esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.40  cnf(c_0_61, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1|~r1_tarski(X1,X2)|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.40  cnf(c_0_63, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_39]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_29])]), c_0_40])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 65
% 0.20/0.40  # Proof object clause steps            : 42
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 6
% 0.20/0.40  # Proof object clause conjectures      : 3
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 14
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 20
% 0.20/0.40  # Proof object simplifying inferences  : 48
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 19
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 16
% 0.20/0.40  # Processed clauses                    : 242
% 0.20/0.40  # ...of these trivial                  : 4
% 0.20/0.40  # ...subsumed                          : 110
% 0.20/0.40  # ...remaining for further processing  : 128
% 0.20/0.40  # Other redundant clauses eliminated   : 24
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 2
% 0.20/0.40  # Backward-rewritten                   : 26
% 0.20/0.40  # Generated clauses                    : 1517
% 0.20/0.40  # ...of the previous two non-trivial   : 1419
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 1477
% 0.20/0.40  # Factorizations                       : 16
% 0.20/0.40  # Equation resolutions                 : 24
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 81
% 0.20/0.40  #    Positive orientable unit clauses  : 7
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 69
% 0.20/0.40  # Current number of unprocessed clauses: 1038
% 0.20/0.40  # ...number of literals in the above   : 4351
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 46
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 861
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 608
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 98
% 0.20/0.40  # Unit Clause-clause subsumption calls : 17
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 10
% 0.20/0.40  # BW rewrite match successes           : 9
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23639
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.056 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.062 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
