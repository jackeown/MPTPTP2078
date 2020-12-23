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
% DateTime   : Thu Dec  3 10:43:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  83 expanded)
%              Number of clauses        :   20 (  38 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 322 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t103_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X4,X1)
          & ! [X5,X6] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & X4 = k4_tarski(X5,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t103_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_6,negated_conjecture,(
    ! [X33,X34] :
      ( r1_tarski(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))
      & r2_hidden(esk9_0,esk6_0)
      & ( ~ r2_hidden(X33,esk7_0)
        | ~ r2_hidden(X34,esk8_0)
        | esk9_0 != k4_tarski(X33,X34) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(k1_tarski(X27),X28)
        | r2_hidden(X27,X28) )
      & ( ~ r2_hidden(X27,X28)
        | r1_tarski(k1_tarski(X27),X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk9_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X16,X17,X18,X19,X20,X21,X23,X24] :
      ( ( r2_hidden(esk1_4(X10,X11,X12,X13),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( r2_hidden(esk2_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( X13 = k4_tarski(esk1_4(X10,X11,X12,X13),esk2_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( ~ r2_hidden(X17,X10)
        | ~ r2_hidden(X18,X11)
        | X16 != k4_tarski(X17,X18)
        | r2_hidden(X16,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( ~ r2_hidden(esk3_3(X19,X20,X21),X21)
        | ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X24,X20)
        | esk3_3(X19,X20,X21) != k4_tarski(X23,X24)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X19)
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk5_3(X19,X20,X21),X20)
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( esk3_3(X19,X20,X21) = k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21))
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k1_tarski(esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k1_tarski(esk9_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | esk9_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(esk1_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk2_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.42  # and selection function SelectNewComplexAHP.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t103_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.20/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.42  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.42  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.42  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t103_zfmisc_1])).
% 0.20/0.42  fof(c_0_5, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.42  fof(c_0_6, negated_conjecture, ![X33, X34]:((r1_tarski(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))&r2_hidden(esk9_0,esk6_0))&(~r2_hidden(X33,esk7_0)|~r2_hidden(X34,esk8_0)|esk9_0!=k4_tarski(X33,X34))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.42  fof(c_0_7, plain, ![X27, X28]:((~r1_tarski(k1_tarski(X27),X28)|r2_hidden(X27,X28))&(~r2_hidden(X27,X28)|r1_tarski(k1_tarski(X27),X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.42  cnf(c_0_8, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.42  cnf(c_0_9, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_10, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_11, negated_conjecture, (r2_hidden(esk9_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  fof(c_0_12, plain, ![X10, X11, X12, X13, X16, X17, X18, X19, X20, X21, X23, X24]:(((((r2_hidden(esk1_4(X10,X11,X12,X13),X10)|~r2_hidden(X13,X12)|X12!=k2_zfmisc_1(X10,X11))&(r2_hidden(esk2_4(X10,X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k2_zfmisc_1(X10,X11)))&(X13=k4_tarski(esk1_4(X10,X11,X12,X13),esk2_4(X10,X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k2_zfmisc_1(X10,X11)))&(~r2_hidden(X17,X10)|~r2_hidden(X18,X11)|X16!=k4_tarski(X17,X18)|r2_hidden(X16,X12)|X12!=k2_zfmisc_1(X10,X11)))&((~r2_hidden(esk3_3(X19,X20,X21),X21)|(~r2_hidden(X23,X19)|~r2_hidden(X24,X20)|esk3_3(X19,X20,X21)!=k4_tarski(X23,X24))|X21=k2_zfmisc_1(X19,X20))&(((r2_hidden(esk4_3(X19,X20,X21),X19)|r2_hidden(esk3_3(X19,X20,X21),X21)|X21=k2_zfmisc_1(X19,X20))&(r2_hidden(esk5_3(X19,X20,X21),X20)|r2_hidden(esk3_3(X19,X20,X21),X21)|X21=k2_zfmisc_1(X19,X20)))&(esk3_3(X19,X20,X21)=k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21))|r2_hidden(esk3_3(X19,X20,X21),X21)|X21=k2_zfmisc_1(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.42  cnf(c_0_13, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk7_0,esk8_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.42  cnf(c_0_14, negated_conjecture, (r1_tarski(k1_tarski(esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.42  cnf(c_0_15, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_17, negated_conjecture, (r1_tarski(k1_tarski(esk9_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.42  cnf(c_0_18, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_19, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_20, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.42  cnf(c_0_22, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.42  cnf(c_0_23, plain, (r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk8_0)|esk9_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (k4_tarski(esk1_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk2_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0))=esk9_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_4(esk7_0,esk8_0,k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 29
% 0.20/0.42  # Proof object clause steps            : 20
% 0.20/0.42  # Proof object formula steps           : 9
% 0.20/0.42  # Proof object conjectures             : 14
% 0.20/0.42  # Proof object clause conjectures      : 11
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 9
% 0.20/0.42  # Proof object initial formulas used   : 4
% 0.20/0.42  # Proof object generating inferences   : 11
% 0.20/0.42  # Proof object simplifying inferences  : 3
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 4
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 14
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 14
% 0.20/0.42  # Processed clauses                    : 209
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 18
% 0.20/0.42  # ...remaining for further processing  : 191
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 0
% 0.20/0.42  # Generated clauses                    : 2996
% 0.20/0.42  # ...of the previous two non-trivial   : 2962
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 2988
% 0.20/0.42  # Factorizations                       : 2
% 0.20/0.42  # Equation resolutions                 : 6
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 191
% 0.20/0.42  #    Positive orientable unit clauses  : 71
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 0
% 0.20/0.42  #    Non-unit-clauses                  : 120
% 0.20/0.42  # Current number of unprocessed clauses: 2767
% 0.20/0.42  # ...number of literals in the above   : 7538
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 0
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 816
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 542
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.42  # Unit Clause-clause subsumption calls : 10
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 51
% 0.20/0.42  # BW rewrite match successes           : 0
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 70117
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.065 s
% 0.20/0.42  # System time              : 0.011 s
% 0.20/0.42  # Total time               : 0.077 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
