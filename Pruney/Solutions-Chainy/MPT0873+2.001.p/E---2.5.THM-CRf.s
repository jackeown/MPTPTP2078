%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 530 expanded)
%              Number of clauses        :   26 ( 278 expanded)
%              Number of leaves         :    6 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 (1328 expanded)
%              Number of equality atoms :   95 (1327 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

fof(c_0_7,plain,(
    ! [X34,X35,X36,X37] : k4_mcart_1(X34,X35,X36,X37) = k4_tarski(k3_mcart_1(X34,X35,X36),X37) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X31,X32,X33] : k3_mcart_1(X31,X32,X33) = k4_tarski(k4_tarski(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = k4_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0)
    & ( esk5_0 != esk9_0
      | esk6_0 != esk10_0
      | esk7_0 != esk11_0
      | esk8_0 != esk12_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | k4_tarski(X9,X10) != k4_tarski(X11,X12) )
      & ( X10 = X12
        | k4_tarski(X9,X10) != k4_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = k4_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( X16 != k1_mcart_1(X13)
        | X13 != k4_tarski(X17,X18)
        | X16 = X17
        | X13 != k4_tarski(X14,X15) )
      & ( X13 = k4_tarski(esk1_2(X13,X19),esk2_2(X13,X19))
        | X19 = k1_mcart_1(X13)
        | X13 != k4_tarski(X14,X15) )
      & ( X19 != esk1_2(X13,X19)
        | X19 = k1_mcart_1(X13)
        | X13 != k4_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0) = k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28] :
      ( ( X25 != k2_mcart_1(X22)
        | X22 != k4_tarski(X26,X27)
        | X25 = X27
        | X22 != k4_tarski(X23,X24) )
      & ( X22 = k4_tarski(esk3_2(X22,X28),esk4_2(X22,X28))
        | X28 = k2_mcart_1(X22)
        | X22 != k4_tarski(X23,X24) )
      & ( X28 != esk4_2(X22,X28)
        | X28 = k2_mcart_1(X22)
        | X22 != k4_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk8_0
    | k4_tarski(X2,X1) != k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = esk12_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_25,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk12_0) = k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_27,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) = k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 = esk11_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(k4_tarski(esk5_0,esk6_0),esk11_0) = k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( esk5_0 != esk9_0
    | esk6_0 != esk10_0
    | esk7_0 != esk11_0
    | esk8_0 != esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(esk5_0,esk6_0) = k4_tarski(esk9_0,esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_30]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != esk9_0
    | esk6_0 != esk10_0
    | esk7_0 != esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_23])])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 = esk10_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 != esk9_0
    | esk6_0 != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(esk5_0,esk10_0) = k4_tarski(esk9_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_36]),c_0_25]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t33_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.12/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.12/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.37  fof(t33_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k4_tarski(X1,X2)=k4_tarski(X3,X4)=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 0.12/0.37  fof(d1_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k1_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_mcart_1)).
% 0.12/0.37  fof(d2_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k2_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_mcart_1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8))), inference(assume_negation,[status(cth)],[t33_mcart_1])).
% 0.12/0.37  fof(c_0_7, plain, ![X34, X35, X36, X37]:k4_mcart_1(X34,X35,X36,X37)=k4_tarski(k3_mcart_1(X34,X35,X36),X37), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.12/0.37  fof(c_0_8, plain, ![X31, X32, X33]:k3_mcart_1(X31,X32,X33)=k4_tarski(k4_tarski(X31,X32),X33), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, (k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=k4_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0)&(esk5_0!=esk9_0|esk6_0!=esk10_0|esk7_0!=esk11_0|esk8_0!=esk12_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.37  cnf(c_0_10, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_12, plain, ![X9, X10, X11, X12]:((X9=X11|k4_tarski(X9,X10)!=k4_tarski(X11,X12))&(X10=X12|k4_tarski(X9,X10)!=k4_tarski(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=k4_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  fof(c_0_15, plain, ![X13, X14, X15, X16, X17, X18, X19]:((X16!=k1_mcart_1(X13)|(X13!=k4_tarski(X17,X18)|X16=X17)|X13!=k4_tarski(X14,X15))&((X13=k4_tarski(esk1_2(X13,X19),esk2_2(X13,X19))|X19=k1_mcart_1(X13)|X13!=k4_tarski(X14,X15))&(X19!=esk1_2(X13,X19)|X19=k1_mcart_1(X13)|X13!=k4_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).
% 0.12/0.37  cnf(c_0_16, plain, (X1=X2|k4_tarski(X3,X1)!=k4_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0)=k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.12/0.37  fof(c_0_18, plain, ![X22, X23, X24, X25, X26, X27, X28]:((X25!=k2_mcart_1(X22)|(X22!=k4_tarski(X26,X27)|X25=X27)|X22!=k4_tarski(X23,X24))&((X22=k4_tarski(esk3_2(X22,X28),esk4_2(X22,X28))|X28=k2_mcart_1(X22)|X22!=k4_tarski(X23,X24))&(X28!=esk4_2(X22,X28)|X28=k2_mcart_1(X22)|X22!=k4_tarski(X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).
% 0.12/0.37  cnf(c_0_19, plain, (X1=X3|X1!=k1_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (X1=esk8_0|k4_tarski(X2,X1)!=k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_21, plain, (X1=X4|X1!=k2_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X3,X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk8_0=esk12_0), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_24, plain, (k2_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X4,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).
% 0.12/0.37  cnf(c_0_25, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk12_0)=k4_tarski(k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0),esk12_0)), inference(rw,[status(thm)],[c_0_17, c_0_23])).
% 0.12/0.37  cnf(c_0_27, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(er,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)=k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_25])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (esk7_0=esk11_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_27])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k4_tarski(k4_tarski(esk5_0,esk6_0),esk11_0)=k4_tarski(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (esk5_0!=esk9_0|esk6_0!=esk10_0|esk7_0!=esk11_0|esk8_0!=esk12_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k4_tarski(esk5_0,esk6_0)=k4_tarski(esk9_0,esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_30]), c_0_25])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (esk5_0!=esk9_0|esk6_0!=esk10_0|esk7_0!=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_23])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (esk6_0=esk10_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_32]), c_0_27])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (esk5_0!=esk9_0|esk6_0!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_29])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k4_tarski(esk5_0,esk10_0)=k4_tarski(esk9_0,esk10_0)), inference(rw,[status(thm)],[c_0_32, c_0_34])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (esk5_0!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_36]), c_0_25]), c_0_37]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 39
% 0.12/0.37  # Proof object clause steps            : 26
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 19
% 0.12/0.37  # Proof object clause conjectures      : 16
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 7
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 22
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 12
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 10
% 0.12/0.37  # Processed clauses                    : 45
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 42
% 0.12/0.37  # Other redundant clauses eliminated   : 8
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 14
% 0.12/0.37  # Generated clauses                    : 94
% 0.12/0.37  # ...of the previous two non-trivial   : 94
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 83
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 13
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
% 0.12/0.37  # Current number of processed clauses  : 12
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 5
% 0.12/0.37  # Current number of unprocessed clauses: 66
% 0.12/0.37  # ...number of literals in the above   : 154
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 26
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 65
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 59
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 9
% 0.12/0.37  # BW rewrite match successes           : 9
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1686
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
