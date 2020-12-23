%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of clauses        :   32 (  40 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 215 expanded)
%              Number of equality atoms :   45 (  75 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_10,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X47,X46)
        | r1_tarski(X47,X45)
        | X46 != k1_zfmisc_1(X45) )
      & ( ~ r1_tarski(X48,X45)
        | r2_hidden(X48,X46)
        | X46 != k1_zfmisc_1(X45) )
      & ( ~ r2_hidden(esk2_2(X49,X50),X50)
        | ~ r1_tarski(esk2_2(X49,X50),X49)
        | X50 = k1_zfmisc_1(X49) )
      & ( r2_hidden(esk2_2(X49,X50),X50)
        | r1_tarski(esk2_2(X49,X50),X49)
        | X50 = k1_zfmisc_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))
    & ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X43,X44] : r1_tarski(X43,k2_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X29,X30] : k2_xboole_0(X29,k4_xboole_0(X30,X29)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_26,plain,(
    ! [X31,X32] : k4_xboole_0(k2_xboole_0(X31,X32),X32) = k4_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk4_0))
    | r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34])).

fof(c_0_41,plain,(
    ! [X20,X21] :
      ( ( ~ r3_xboole_0(X20,X21)
        | r1_tarski(X20,X21)
        | r1_tarski(X21,X20) )
      & ( ~ r1_tarski(X20,X21)
        | r3_xboole_0(X20,X21) )
      & ( ~ r1_tarski(X21,X20)
        | r3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r2_hidden(k2_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0
    | r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0
    | k2_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.017 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t82_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 0.13/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.13/0.38  fof(c_0_10, plain, ![X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X47,X46)|r1_tarski(X47,X45)|X46!=k1_zfmisc_1(X45))&(~r1_tarski(X48,X45)|r2_hidden(X48,X46)|X46!=k1_zfmisc_1(X45)))&((~r2_hidden(esk2_2(X49,X50),X50)|~r1_tarski(esk2_2(X49,X50),X49)|X50=k1_zfmisc_1(X49))&(r2_hidden(esk2_2(X49,X50),X50)|r1_tarski(esk2_2(X49,X50),X49)|X50=k1_zfmisc_1(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t82_zfmisc_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))=k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))&~r3_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X43, X44]:r1_tarski(X43,k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.38  fof(c_0_20, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))=k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_25, plain, ![X29, X30]:k2_xboole_0(X29,k4_xboole_0(X30,X29))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.38  fof(c_0_26, plain, ![X31, X32]:k4_xboole_0(k2_xboole_0(X31,X32),X32)=k4_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.13/0.38  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  fof(c_0_33, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk4_0))|r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34])).
% 0.13/0.38  fof(c_0_41, plain, ![X20, X21]:((~r3_xboole_0(X20,X21)|(r1_tarski(X20,X21)|r1_tarski(X21,X20)))&((~r1_tarski(X20,X21)|r3_xboole_0(X20,X21))&(~r1_tarski(X21,X20)|r3_xboole_0(X20,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.13/0.38  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=X1|~r2_hidden(k2_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0|r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_39])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (~r3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_45, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0|k2_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_48, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_39])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_46]), c_0_47])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_48])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 53
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 14
% 0.13/0.38  # Proof object simplifying inferences  : 10
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 19
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 31
% 0.13/0.38  # Processed clauses                    : 377
% 0.13/0.38  # ...of these trivial                  : 101
% 0.13/0.38  # ...subsumed                          : 102
% 0.13/0.38  # ...remaining for further processing  : 174
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 13
% 0.13/0.38  # Generated clauses                    : 2259
% 0.13/0.38  # ...of the previous two non-trivial   : 1406
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 2245
% 0.13/0.38  # Factorizations                       : 7
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 124
% 0.13/0.38  #    Positive orientable unit clauses  : 77
% 0.13/0.38  #    Positive unorientable unit clauses: 6
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 36
% 0.13/0.38  # Current number of unprocessed clauses: 1078
% 0.13/0.38  # ...number of literals in the above   : 1527
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 44
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 315
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 290
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 33
% 0.13/0.38  # Unit Clause-clause subsumption calls : 96
% 0.13/0.38  # Rewrite failures with RHS unbound    : 39
% 0.13/0.38  # BW rewrite match attempts            : 141
% 0.13/0.38  # BW rewrite match successes           : 25
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 21562
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
