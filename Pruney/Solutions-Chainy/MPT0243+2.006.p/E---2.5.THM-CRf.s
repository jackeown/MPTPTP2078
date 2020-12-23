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
% DateTime   : Thu Dec  3 10:39:29 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of clauses        :   42 (  69 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  176 ( 481 expanded)
%              Number of equality atoms :   53 ( 151 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t25_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0) )
    & ( r2_hidden(esk4_0,esk5_0)
      | r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X27
        | X31 = X28
        | X31 = X29
        | X30 != k1_enumset1(X27,X28,X29) )
      & ( X32 != X27
        | r2_hidden(X32,X30)
        | X30 != k1_enumset1(X27,X28,X29) )
      & ( X32 != X28
        | r2_hidden(X32,X30)
        | X30 != k1_enumset1(X27,X28,X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k1_enumset1(X27,X28,X29) )
      & ( esk2_4(X33,X34,X35,X36) != X33
        | ~ r2_hidden(esk2_4(X33,X34,X35,X36),X36)
        | X36 = k1_enumset1(X33,X34,X35) )
      & ( esk2_4(X33,X34,X35,X36) != X34
        | ~ r2_hidden(esk2_4(X33,X34,X35,X36),X36)
        | X36 = k1_enumset1(X33,X34,X35) )
      & ( esk2_4(X33,X34,X35,X36) != X35
        | ~ r2_hidden(esk2_4(X33,X34,X35,X36),X36)
        | X36 = k1_enumset1(X33,X34,X35) )
      & ( r2_hidden(esk2_4(X33,X34,X35,X36),X36)
        | esk2_4(X33,X34,X35,X36) = X33
        | esk2_4(X33,X34,X35,X36) = X34
        | esk2_4(X33,X34,X35,X36) = X35
        | X36 = k1_enumset1(X33,X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X40,X41] :
      ( ( ~ r1_tarski(k1_tarski(X40),X41)
        | r2_hidden(X40,X41) )
      & ( ~ r2_hidden(X40,X41)
        | r1_tarski(k1_tarski(X40),X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_tarski(k1_tarski(X44),k2_tarski(X45,X46))
      | X44 = X45
      | X44 = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k2_xboole_0(X20,X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r1_tarski(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(k2_xboole_0(X17,X18),X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( esk1_2(k1_enumset1(X1,X1,X2),X3) = X1
    | esk1_2(k1_enumset1(X1,X1,X2),X3) = X2
    | r1_tarski(k1_enumset1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,plain,
    ( esk1_2(k1_enumset1(X1,X1,X2),X3) = X1
    | r1_tarski(k1_enumset1(X1,X1,X2),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tarski(esk4_0))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0)
    | ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X2),X3)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(esk4_0))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0)
    | ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_26])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_enumset1(esk3_0,esk3_0,X1),esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_55])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.35/4.56  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 4.35/4.56  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.35/4.56  #
% 4.35/4.56  # Preprocessing time       : 0.028 s
% 4.35/4.56  # Presaturation interreduction done
% 4.35/4.56  
% 4.35/4.56  # Proof found!
% 4.35/4.56  # SZS status Theorem
% 4.35/4.56  # SZS output start CNFRefutation
% 4.35/4.56  fof(t38_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.35/4.56  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.35/4.56  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.35/4.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.35/4.56  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.35/4.56  fof(t25_zfmisc_1, axiom, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.35/4.56  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.35/4.56  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.35/4.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.35/4.56  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t38_zfmisc_1])).
% 4.35/4.56  fof(c_0_10, negated_conjecture, ((~r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0))&(r2_hidden(esk4_0,esk5_0)|r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 4.35/4.56  fof(c_0_11, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.35/4.56  fof(c_0_12, plain, ![X27, X28, X29, X30, X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X31,X30)|(X31=X27|X31=X28|X31=X29)|X30!=k1_enumset1(X27,X28,X29))&(((X32!=X27|r2_hidden(X32,X30)|X30!=k1_enumset1(X27,X28,X29))&(X32!=X28|r2_hidden(X32,X30)|X30!=k1_enumset1(X27,X28,X29)))&(X32!=X29|r2_hidden(X32,X30)|X30!=k1_enumset1(X27,X28,X29))))&((((esk2_4(X33,X34,X35,X36)!=X33|~r2_hidden(esk2_4(X33,X34,X35,X36),X36)|X36=k1_enumset1(X33,X34,X35))&(esk2_4(X33,X34,X35,X36)!=X34|~r2_hidden(esk2_4(X33,X34,X35,X36),X36)|X36=k1_enumset1(X33,X34,X35)))&(esk2_4(X33,X34,X35,X36)!=X35|~r2_hidden(esk2_4(X33,X34,X35,X36),X36)|X36=k1_enumset1(X33,X34,X35)))&(r2_hidden(esk2_4(X33,X34,X35,X36),X36)|(esk2_4(X33,X34,X35,X36)=X33|esk2_4(X33,X34,X35,X36)=X34|esk2_4(X33,X34,X35,X36)=X35)|X36=k1_enumset1(X33,X34,X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 4.35/4.56  fof(c_0_13, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.35/4.56  cnf(c_0_14, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.35/4.56  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.35/4.56  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.35/4.56  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.35/4.56  cnf(c_0_18, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 4.35/4.56  cnf(c_0_19, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X1)), inference(er,[status(thm)],[c_0_16])).
% 4.35/4.56  fof(c_0_20, plain, ![X40, X41]:((~r1_tarski(k1_tarski(X40),X41)|r2_hidden(X40,X41))&(~r2_hidden(X40,X41)|r1_tarski(k1_tarski(X40),X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 4.35/4.56  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 4.35/4.56  cnf(c_0_22, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[c_0_19])).
% 4.35/4.56  fof(c_0_23, plain, ![X44, X45, X46]:(~r1_tarski(k1_tarski(X44),k2_tarski(X45,X46))|X44=X45|X44=X46), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).
% 4.35/4.56  fof(c_0_24, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k2_xboole_0(X20,X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.35/4.56  cnf(c_0_25, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.35/4.56  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 4.35/4.56  cnf(c_0_27, plain, (X1=X2|X1=X3|~r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.35/4.56  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.35/4.56  fof(c_0_29, plain, ![X17, X18, X19]:(~r1_tarski(k2_xboole_0(X17,X18),X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 4.35/4.56  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.35/4.56  cnf(c_0_31, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.35/4.56  cnf(c_0_32, plain, (X1=X3|X1=X2|~r1_tarski(k1_tarski(X1),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[c_0_27, c_0_15])).
% 4.35/4.56  cnf(c_0_33, plain, (r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 4.35/4.56  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.35/4.56  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.35/4.56  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.35/4.56  cnf(c_0_37, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.35/4.56  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.35/4.56  cnf(c_0_39, plain, (esk1_2(k1_enumset1(X1,X1,X2),X3)=X1|esk1_2(k1_enumset1(X1,X1,X2),X3)=X2|r1_tarski(k1_enumset1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.35/4.56  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_34, c_0_15])).
% 4.35/4.56  cnf(c_0_41, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X1,X4)), inference(er,[status(thm)],[c_0_35])).
% 4.35/4.56  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.35/4.56  fof(c_0_43, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.35/4.56  cnf(c_0_44, negated_conjecture, (~r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.35/4.56  cnf(c_0_45, plain, (esk1_2(k1_enumset1(X1,X1,X2),X3)=X1|r1_tarski(k1_enumset1(X1,X1,X2),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.35/4.56  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_40])).
% 4.35/4.56  cnf(c_0_47, plain, (r2_hidden(X1,k1_enumset1(X2,X1,X3))), inference(er,[status(thm)],[c_0_41])).
% 4.35/4.56  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_tarski(esk4_0))|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_17, c_0_42])).
% 4.35/4.56  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.35/4.56  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.35/4.56  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)|~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_44, c_0_15])).
% 4.35/4.56  cnf(c_0_52, plain, (r1_tarski(k1_enumset1(X1,X1,X2),X3)|~r2_hidden(X1,X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 4.35/4.56  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 4.35/4.56  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),k1_tarski(esk4_0))|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.35/4.56  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50])).
% 4.35/4.56  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)|~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_26])])).
% 4.35/4.56  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_enumset1(esk3_0,esk3_0,X1),esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 4.35/4.56  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_0,X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 4.35/4.56  cnf(c_0_59, negated_conjecture, (~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_53])])).
% 4.35/4.56  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_55])]), c_0_59]), ['proof']).
% 4.35/4.56  # SZS output end CNFRefutation
% 4.35/4.56  # Proof object total steps             : 61
% 4.35/4.56  # Proof object clause steps            : 42
% 4.35/4.56  # Proof object formula steps           : 19
% 4.35/4.56  # Proof object conjectures             : 23
% 4.35/4.56  # Proof object clause conjectures      : 20
% 4.35/4.56  # Proof object formula conjectures     : 3
% 4.35/4.56  # Proof object initial clauses used    : 15
% 4.35/4.56  # Proof object initial formulas used   : 9
% 4.35/4.56  # Proof object generating inferences   : 18
% 4.35/4.56  # Proof object simplifying inferences  : 14
% 4.35/4.56  # Training examples: 0 positive, 0 negative
% 4.35/4.56  # Parsed axioms                        : 13
% 4.35/4.56  # Removed by relevancy pruning/SinE    : 0
% 4.35/4.56  # Initial clauses                      : 27
% 4.35/4.56  # Removed in clause preprocessing      : 1
% 4.35/4.56  # Initial clauses in saturation        : 26
% 4.35/4.56  # Processed clauses                    : 36950
% 4.35/4.56  # ...of these trivial                  : 911
% 4.35/4.56  # ...subsumed                          : 32878
% 4.35/4.56  # ...remaining for further processing  : 3161
% 4.35/4.56  # Other redundant clauses eliminated   : 244
% 4.35/4.56  # Clauses deleted for lack of memory   : 0
% 4.35/4.56  # Backward-subsumed                    : 84
% 4.35/4.56  # Backward-rewritten                   : 58
% 4.35/4.56  # Generated clauses                    : 617560
% 4.35/4.56  # ...of the previous two non-trivial   : 501373
% 4.35/4.56  # Contextual simplify-reflections      : 13
% 4.35/4.56  # Paramodulations                      : 617227
% 4.35/4.56  # Factorizations                       : 85
% 4.35/4.56  # Equation resolutions                 : 248
% 4.35/4.56  # Propositional unsat checks           : 0
% 4.35/4.56  #    Propositional check models        : 0
% 4.35/4.56  #    Propositional check unsatisfiable : 0
% 4.35/4.56  #    Propositional clauses             : 0
% 4.35/4.56  #    Propositional clauses after purity: 0
% 4.35/4.56  #    Propositional unsat core size     : 0
% 4.35/4.56  #    Propositional preprocessing time  : 0.000
% 4.35/4.56  #    Propositional encoding time       : 0.000
% 4.35/4.56  #    Propositional solver time         : 0.000
% 4.35/4.56  #    Success case prop preproc time    : 0.000
% 4.35/4.56  #    Success case prop encoding time   : 0.000
% 4.35/4.56  #    Success case prop solver time     : 0.000
% 4.35/4.56  # Current number of processed clauses  : 2989
% 4.35/4.56  #    Positive orientable unit clauses  : 434
% 4.35/4.56  #    Positive unorientable unit clauses: 0
% 4.35/4.56  #    Negative unit clauses             : 3
% 4.35/4.56  #    Non-unit-clauses                  : 2552
% 4.35/4.56  # Current number of unprocessed clauses: 463727
% 4.35/4.56  # ...number of literals in the above   : 1341789
% 4.35/4.56  # Current number of archived formulas  : 0
% 4.35/4.56  # Current number of archived clauses   : 168
% 4.35/4.56  # Clause-clause subsumption calls (NU) : 1457397
% 4.35/4.56  # Rec. Clause-clause subsumption calls : 1106563
% 4.35/4.56  # Non-unit clause-clause subsumptions  : 32968
% 4.35/4.56  # Unit Clause-clause subsumption calls : 2419
% 4.35/4.56  # Rewrite failures with RHS unbound    : 0
% 4.35/4.56  # BW rewrite match attempts            : 10017
% 4.35/4.56  # BW rewrite match successes           : 48
% 4.35/4.56  # Condensation attempts                : 0
% 4.35/4.56  # Condensation successes               : 0
% 4.35/4.56  # Termbank termtop insertions          : 8606056
% 4.42/4.58  
% 4.42/4.58  # -------------------------------------------------
% 4.42/4.58  # User time                : 4.070 s
% 4.42/4.58  # System time              : 0.164 s
% 4.42/4.58  # Total time               : 4.234 s
% 4.42/4.58  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
