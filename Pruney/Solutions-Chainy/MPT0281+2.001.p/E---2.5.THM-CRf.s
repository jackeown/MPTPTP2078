%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 168 expanded)
%              Number of clauses        :   42 (  83 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 384 expanded)
%              Number of equality atoms :   44 ( 154 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_10,plain,(
    ! [X46,X47] : k3_tarski(k2_tarski(X46,X47)) = k2_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X41,X40)
        | r1_tarski(X41,X39)
        | X40 != k1_zfmisc_1(X39) )
      & ( ~ r1_tarski(X42,X39)
        | r2_hidden(X42,X40)
        | X40 != k1_zfmisc_1(X39) )
      & ( ~ r2_hidden(esk3_2(X43,X44),X44)
        | ~ r1_tarski(esk3_2(X43,X44),X43)
        | X44 = k1_zfmisc_1(X43) )
      & ( r2_hidden(esk3_2(X43,X44),X44)
        | r1_tarski(esk3_2(X43,X44),X43)
        | X44 = k1_zfmisc_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)) = k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))
    & ~ r3_xboole_0(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)) = k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k3_tarski(k1_enumset1(X3,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))) = k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_21]),c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_38,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k4_xboole_0(k4_xboole_0(k1_zfmisc_1(X1),X2),X3))
    | r2_hidden(X1,X2)
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ( ~ r3_xboole_0(X17,X18)
        | r1_tarski(X17,X18)
        | r1_tarski(X18,X17) )
      & ( ~ r1_tarski(X17,X18)
        | r3_xboole_0(X17,X18) )
      & ( ~ r1_tarski(X18,X17)
        | r3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_21])).

cnf(c_0_48,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_15]),c_0_15])).

cnf(c_0_49,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk5_0
    | r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r3_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_58,plain,
    ( r3_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_57])).

cnf(c_0_60,plain,
    ( r3_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_59]),c_0_47])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.55  # and selection function SelectNegativeLiterals.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.028 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.55  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.55  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.55  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.55  fof(t82_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 0.20/0.55  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.55  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.55  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.55  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.20/0.55  fof(c_0_10, plain, ![X46, X47]:k3_tarski(k2_tarski(X46,X47))=k2_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.55  fof(c_0_11, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.55  fof(c_0_12, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.55  fof(c_0_13, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.55  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.55  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t82_zfmisc_1])).
% 0.20/0.55  fof(c_0_17, plain, ![X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X41,X40)|r1_tarski(X41,X39)|X40!=k1_zfmisc_1(X39))&(~r1_tarski(X42,X39)|r2_hidden(X42,X40)|X40!=k1_zfmisc_1(X39)))&((~r2_hidden(esk3_2(X43,X44),X44)|~r1_tarski(esk3_2(X43,X44),X43)|X44=k1_zfmisc_1(X43))&(r2_hidden(esk3_2(X43,X44),X44)|r1_tarski(esk3_2(X43,X44),X43)|X44=k1_zfmisc_1(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.55  fof(c_0_18, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.55  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.55  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.55  fof(c_0_22, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))=k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))&~r3_xboole_0(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.55  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.55  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_25, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.55  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.55  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))=k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.55  cnf(c_0_28, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_29, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.56  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.56  cnf(c_0_31, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))|~r2_hidden(X1,k3_tarski(k1_enumset1(X3,X3,X4)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.56  cnf(c_0_32, negated_conjecture, (k3_tarski(k1_enumset1(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)))=k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_21]), c_0_21])).
% 0.20/0.56  cnf(c_0_33, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.56  cnf(c_0_34, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.56  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)))|~r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.56  cnf(c_0_36, plain, (r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.56  fof(c_0_37, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.56  fof(c_0_38, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.56  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.56  cnf(c_0_40, negated_conjecture, (~r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.56  cnf(c_0_41, plain, (r2_hidden(X1,k4_xboole_0(k4_xboole_0(k1_zfmisc_1(X1),X2),X3))|r2_hidden(X1,X2)|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_36])).
% 0.20/0.56  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.56  cnf(c_0_43, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.56  fof(c_0_44, plain, ![X17, X18]:((~r3_xboole_0(X17,X18)|(r1_tarski(X17,X18)|r1_tarski(X18,X17)))&((~r1_tarski(X17,X18)|r3_xboole_0(X17,X18))&(~r1_tarski(X18,X17)|r3_xboole_0(X17,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.20/0.56  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.56  cnf(c_0_46, negated_conjecture, (r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.56  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_42, c_0_21])).
% 0.20/0.56  cnf(c_0_48, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_15]), c_0_15])).
% 0.20/0.56  cnf(c_0_49, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.56  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.56  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)|r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.56  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.56  cnf(c_0_53, plain, (r3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_47])).
% 0.20/0.56  cnf(c_0_54, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk5_0|r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.20/0.56  cnf(c_0_55, negated_conjecture, (~r3_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.56  cnf(c_0_56, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.56  cnf(c_0_57, negated_conjecture, (r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.20/0.56  cnf(c_0_58, plain, (r3_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 0.20/0.56  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_57])).
% 0.20/0.56  cnf(c_0_60, plain, (r3_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 0.20/0.56  cnf(c_0_61, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_59]), c_0_47])])).
% 0.20/0.56  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_55]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 63
% 0.20/0.56  # Proof object clause steps            : 42
% 0.20/0.56  # Proof object formula steps           : 21
% 0.20/0.56  # Proof object conjectures             : 15
% 0.20/0.56  # Proof object clause conjectures      : 12
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 15
% 0.20/0.56  # Proof object initial formulas used   : 10
% 0.20/0.56  # Proof object generating inferences   : 17
% 0.20/0.56  # Proof object simplifying inferences  : 18
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 11
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 31
% 0.20/0.56  # Removed in clause preprocessing      : 2
% 0.20/0.56  # Initial clauses in saturation        : 29
% 0.20/0.56  # Processed clauses                    : 889
% 0.20/0.56  # ...of these trivial                  : 8
% 0.20/0.56  # ...subsumed                          : 499
% 0.20/0.56  # ...remaining for further processing  : 382
% 0.20/0.56  # Other redundant clauses eliminated   : 41
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 13
% 0.20/0.56  # Backward-rewritten                   : 180
% 0.20/0.56  # Generated clauses                    : 13256
% 0.20/0.56  # ...of the previous two non-trivial   : 13114
% 0.20/0.56  # Contextual simplify-reflections      : 1
% 0.20/0.56  # Paramodulations                      : 13212
% 0.20/0.56  # Factorizations                       : 6
% 0.20/0.56  # Equation resolutions                 : 41
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 150
% 0.20/0.56  #    Positive orientable unit clauses  : 16
% 0.20/0.56  #    Positive unorientable unit clauses: 2
% 0.20/0.56  #    Negative unit clauses             : 25
% 0.20/0.56  #    Non-unit-clauses                  : 107
% 0.20/0.56  # Current number of unprocessed clauses: 12106
% 0.20/0.56  # ...number of literals in the above   : 62544
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 223
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 13944
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 5577
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 319
% 0.20/0.56  # Unit Clause-clause subsumption calls : 2153
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 79
% 0.20/0.56  # BW rewrite match successes           : 58
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 322738
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.198 s
% 0.20/0.56  # System time              : 0.018 s
% 0.20/0.56  # Total time               : 0.216 s
% 0.20/0.56  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
