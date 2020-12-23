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
% DateTime   : Thu Dec  3 10:52:14 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 264 expanded)
%              Number of clauses        :   40 ( 118 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 463 expanded)
%              Number of equality atoms :   68 ( 267 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23] : k2_enumset1(X20,X21,X22,X23) = k2_xboole_0(k2_tarski(X20,X21),k2_tarski(X22,X23)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_16,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,k1_tarski(X26)) != X25
        | ~ r2_hidden(X26,X25) )
      & ( r2_hidden(X26,X25)
        | k4_xboole_0(X25,k1_tarski(X26)) = X25 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X24] : k2_enumset1(X24,X24,X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X5] : k2_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_22,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | k11_relat_1(X31,X32) = k9_relat_1(X31,k1_tarski(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | k9_relat_1(X48,X47) = k9_relat_1(X48,k3_xboole_0(k1_relat_1(X48),X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

fof(c_0_30,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X2,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

fof(c_0_34,plain,(
    ! [X17] :
      ( ( r1_xboole_0(X17,X17)
        | X17 != k1_xboole_0 )
      & ( X17 = k1_xboole_0
        | ~ r1_xboole_0(X17,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_35,plain,(
    ! [X18,X19] : r1_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_36,plain,(
    ! [X49] :
      ( ~ v1_relat_1(X49)
      | k9_relat_1(X49,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

cnf(c_0_37,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X2,X2))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25]),c_0_26])).

cnf(c_0_38,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) = X1
    | r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_47,plain,(
    ! [X50,X51,X52] :
      ( ( ~ r2_hidden(k4_tarski(X50,X51),X52)
        | r2_hidden(X51,k11_relat_1(X52,X50))
        | ~ v1_relat_1(X52) )
      & ( ~ r2_hidden(X51,k11_relat_1(X52,X50))
        | r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X2)) = k11_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_49,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk6_0),k2_tarski(esk5_0,esk5_0)) = k1_relat_1(esk6_0)
    | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X2,X2)))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_25]),c_0_26])).

fof(c_0_54,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(esk6_0,k2_tarski(X1,X1)) = k11_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0)) = k1_xboole_0
    | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_45])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk6_0,k2_tarski(X2,X2)))
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_45])])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | r2_hidden(k4_tarski(X35,esk2_3(X33,X34,X35)),X33)
        | X34 != k1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X37,X38),X33)
        | r2_hidden(X37,X34)
        | X34 != k1_relat_1(X33) )
      & ( ~ r2_hidden(esk3_2(X39,X40),X40)
        | ~ r2_hidden(k4_tarski(esk3_2(X39,X40),X42),X39)
        | X40 = k1_relat_1(X39) )
      & ( r2_hidden(esk3_2(X39,X40),X40)
        | r2_hidden(k4_tarski(esk3_2(X39,X40),esk4_2(X39,X40)),X39)
        | X40 = k1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,X1),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( X1 != k1_relat_1(esk6_0)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_61])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.21/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.21/0.42  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.21/0.42  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.21/0.42  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.42  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.21/0.42  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.21/0.42  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 0.21/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.42  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.21/0.42  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.21/0.42  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 0.21/0.42  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.21/0.42  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.21/0.42  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.42  fof(c_0_15, plain, ![X20, X21, X22, X23]:k2_enumset1(X20,X21,X22,X23)=k2_xboole_0(k2_tarski(X20,X21),k2_tarski(X22,X23)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.21/0.42  fof(c_0_16, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.21/0.42  fof(c_0_17, plain, ![X25, X26]:((k4_xboole_0(X25,k1_tarski(X26))!=X25|~r2_hidden(X26,X25))&(r2_hidden(X26,X25)|k4_xboole_0(X25,k1_tarski(X26))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.21/0.42  fof(c_0_18, plain, ![X24]:k2_enumset1(X24,X24,X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.42  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  fof(c_0_21, plain, ![X5]:k2_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.42  fof(c_0_22, plain, ![X31, X32]:(~v1_relat_1(X31)|k11_relat_1(X31,X32)=k9_relat_1(X31,k1_tarski(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.21/0.42  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.21/0.42  cnf(c_0_24, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.42  cnf(c_0_27, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  fof(c_0_29, plain, ![X47, X48]:(~v1_relat_1(X48)|k9_relat_1(X48,X47)=k9_relat_1(X48,k3_xboole_0(k1_relat_1(X48),X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.21/0.42  fof(c_0_30, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.42  fof(c_0_31, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0)&(r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.21/0.42  cnf(c_0_32, plain, (k4_xboole_0(X2,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.21/0.42  cnf(c_0_33, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_27, c_0_20])).
% 0.21/0.42  fof(c_0_34, plain, ![X17]:((r1_xboole_0(X17,X17)|X17!=k1_xboole_0)&(X17=k1_xboole_0|~r1_xboole_0(X17,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.21/0.42  fof(c_0_35, plain, ![X18, X19]:r1_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.21/0.42  fof(c_0_36, plain, ![X49]:(~v1_relat_1(X49)|k9_relat_1(X49,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.21/0.42  cnf(c_0_37, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X2,X2))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25]), c_0_26])).
% 0.21/0.42  cnf(c_0_38, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))=X1|r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.42  cnf(c_0_42, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.42  cnf(c_0_44, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_46, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  fof(c_0_47, plain, ![X50, X51, X52]:((~r2_hidden(k4_tarski(X50,X51),X52)|r2_hidden(X51,k11_relat_1(X52,X50))|~v1_relat_1(X52))&(~r2_hidden(X51,k11_relat_1(X52,X50))|r2_hidden(k4_tarski(X50,X51),X52)|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.21/0.42  cnf(c_0_48, plain, (k9_relat_1(X1,k2_tarski(X2,X2))=k11_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_37, c_0_33])).
% 0.21/0.42  cnf(c_0_49, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_relat_1(esk6_0),k2_tarski(esk5_0,esk5_0))=k1_relat_1(esk6_0)|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.42  cnf(c_0_51, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.42  cnf(c_0_52, negated_conjecture, (k9_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.42  cnf(c_0_53, plain, (k4_xboole_0(X1,k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X2,X2))))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_25]), c_0_26])).
% 0.21/0.42  fof(c_0_54, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.21/0.42  cnf(c_0_55, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (k9_relat_1(esk6_0,k2_tarski(X1,X1))=k11_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.21/0.42  cnf(c_0_57, negated_conjecture, (k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0))=k1_xboole_0|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_45])])).
% 0.21/0.42  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_53, c_0_33])).
% 0.21/0.42  cnf(c_0_59, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk6_0,k2_tarski(X2,X2)))|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_45])])).
% 0.21/0.42  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56])])).
% 0.21/0.42  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.42  fof(c_0_63, plain, ![X33, X34, X35, X37, X38, X39, X40, X42]:(((~r2_hidden(X35,X34)|r2_hidden(k4_tarski(X35,esk2_3(X33,X34,X35)),X33)|X34!=k1_relat_1(X33))&(~r2_hidden(k4_tarski(X37,X38),X33)|r2_hidden(X37,X34)|X34!=k1_relat_1(X33)))&((~r2_hidden(esk3_2(X39,X40),X40)|~r2_hidden(k4_tarski(esk3_2(X39,X40),X42),X39)|X40=k1_relat_1(X39))&(r2_hidden(esk3_2(X39,X40),X40)|r2_hidden(k4_tarski(esk3_2(X39,X40),esk4_2(X39,X40)),X39)|X40=k1_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.42  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (~r2_hidden(k4_tarski(esk5_0,X1),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.21/0.42  cnf(c_0_66, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.42  cnf(c_0_67, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k9_relat_1(esk6_0,k2_tarski(esk5_0,esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_56])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (X1!=k1_relat_1(esk6_0)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_61])])).
% 0.21/0.42  cnf(c_0_70, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 71
% 0.21/0.42  # Proof object clause steps            : 40
% 0.21/0.42  # Proof object formula steps           : 31
% 0.21/0.42  # Proof object conjectures             : 17
% 0.21/0.42  # Proof object clause conjectures      : 14
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 18
% 0.21/0.42  # Proof object initial formulas used   : 15
% 0.21/0.42  # Proof object generating inferences   : 10
% 0.21/0.42  # Proof object simplifying inferences  : 24
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 22
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 33
% 0.21/0.42  # Removed in clause preprocessing      : 5
% 0.21/0.42  # Initial clauses in saturation        : 28
% 0.21/0.42  # Processed clauses                    : 642
% 0.21/0.42  # ...of these trivial                  : 56
% 0.21/0.42  # ...subsumed                          : 311
% 0.21/0.42  # ...remaining for further processing  : 275
% 0.21/0.42  # Other redundant clauses eliminated   : 0
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 21
% 0.21/0.42  # Backward-rewritten                   : 25
% 0.21/0.42  # Generated clauses                    : 2834
% 0.21/0.42  # ...of the previous two non-trivial   : 1978
% 0.21/0.42  # Contextual simplify-reflections      : 3
% 0.21/0.42  # Paramodulations                      : 2772
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 47
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 195
% 0.21/0.42  #    Positive orientable unit clauses  : 26
% 0.21/0.42  #    Positive unorientable unit clauses: 1
% 0.21/0.42  #    Negative unit clauses             : 7
% 0.21/0.42  #    Non-unit-clauses                  : 161
% 0.21/0.42  # Current number of unprocessed clauses: 1365
% 0.21/0.42  # ...number of literals in the above   : 5278
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 79
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 2486
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 2122
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 214
% 0.21/0.42  # Unit Clause-clause subsumption calls : 331
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 22
% 0.21/0.42  # BW rewrite match successes           : 11
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 31283
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.073 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.080 s
% 0.21/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
