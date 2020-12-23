%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:20 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  70 expanded)
%              Number of clauses        :   19 (  33 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 280 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t99_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t99_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | r1_tarski(X15,X13)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r1_tarski(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    k3_tarski(k1_zfmisc_1(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(X22,esk3_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X27)
        | ~ r2_hidden(esk4_2(X26,X27),X29)
        | ~ r2_hidden(X29,X26)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X26)
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

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

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk5_2(k1_zfmisc_1(esk6_0),esk6_0),k1_zfmisc_1(esk6_0))
    | r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)
    | r1_tarski(esk5_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_2(k1_zfmisc_1(esk6_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk5_2(k1_zfmisc_1(esk6_0),esk6_0))
    | r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_22])])).

cnf(c_0_27,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | ~ r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2)
    | ~ r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:06:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.18/0.45  # and selection function SelectDivPreferIntoLits.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.028 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t99_zfmisc_1, conjecture, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.18/0.45  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.18/0.45  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.18/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.45  fof(c_0_5, negated_conjecture, ~(![X1]:k3_tarski(k1_zfmisc_1(X1))=X1), inference(assume_negation,[status(cth)],[t99_zfmisc_1])).
% 0.18/0.45  fof(c_0_6, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|r1_tarski(X15,X13)|X14!=k1_zfmisc_1(X13))&(~r1_tarski(X16,X13)|r2_hidden(X16,X14)|X14!=k1_zfmisc_1(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|~r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17))&(r2_hidden(esk2_2(X17,X18),X18)|r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.18/0.45  fof(c_0_7, negated_conjecture, k3_tarski(k1_zfmisc_1(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.18/0.45  fof(c_0_8, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:((((r2_hidden(X22,esk3_3(X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k3_tarski(X20))&(r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k3_tarski(X20)))&(~r2_hidden(X24,X25)|~r2_hidden(X25,X20)|r2_hidden(X24,X21)|X21!=k3_tarski(X20)))&((~r2_hidden(esk4_2(X26,X27),X27)|(~r2_hidden(esk4_2(X26,X27),X29)|~r2_hidden(X29,X26))|X27=k3_tarski(X26))&((r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))&(r2_hidden(esk5_2(X26,X27),X26)|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.18/0.45  fof(c_0_9, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.45  cnf(c_0_10, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.45  cnf(c_0_11, negated_conjecture, (k3_tarski(k1_zfmisc_1(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.45  cnf(c_0_12, plain, (r2_hidden(esk5_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.45  cnf(c_0_13, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.45  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.45  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.45  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_17, negated_conjecture, (r2_hidden(esk5_2(k1_zfmisc_1(esk6_0),esk6_0),k1_zfmisc_1(esk6_0))|r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12])])).
% 0.18/0.45  cnf(c_0_18, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.18/0.45  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.45  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)|r1_tarski(esk5_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.45  cnf(c_0_22, plain, (r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.45  cnf(c_0_23, plain, (X2=k3_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(esk4_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.45  cnf(c_0_24, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.45  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_2(k1_zfmisc_1(esk6_0),esk6_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.45  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk5_2(k1_zfmisc_1(esk6_0),esk6_0))|r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_22])])).
% 0.18/0.45  cnf(c_0_27, plain, (X1=k3_tarski(k1_zfmisc_1(X2))|~r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2)|~r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.45  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_2(k1_zfmisc_1(esk6_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.45  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])]), c_0_11]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 30
% 0.18/0.45  # Proof object clause steps            : 19
% 0.18/0.45  # Proof object formula steps           : 11
% 0.18/0.45  # Proof object conjectures             : 10
% 0.18/0.45  # Proof object clause conjectures      : 7
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 8
% 0.18/0.45  # Proof object initial formulas used   : 5
% 0.18/0.45  # Proof object generating inferences   : 8
% 0.18/0.45  # Proof object simplifying inferences  : 8
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 5
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 17
% 0.18/0.45  # Removed in clause preprocessing      : 0
% 0.18/0.45  # Initial clauses in saturation        : 17
% 0.18/0.45  # Processed clauses                    : 182
% 0.18/0.45  # ...of these trivial                  : 0
% 0.18/0.45  # ...subsumed                          : 6
% 0.18/0.45  # ...remaining for further processing  : 176
% 0.18/0.45  # Other redundant clauses eliminated   : 51
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 0
% 0.18/0.45  # Backward-rewritten                   : 9
% 0.18/0.45  # Generated clauses                    : 5903
% 0.18/0.45  # ...of the previous two non-trivial   : 5844
% 0.18/0.45  # Contextual simplify-reflections      : 1
% 0.18/0.45  # Paramodulations                      : 5852
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 51
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 144
% 0.18/0.45  #    Positive orientable unit clauses  : 65
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 1
% 0.18/0.45  #    Non-unit-clauses                  : 78
% 0.18/0.45  # Current number of unprocessed clauses: 5683
% 0.18/0.45  # ...number of literals in the above   : 17434
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 25
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 625
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 511
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 7
% 0.18/0.45  # Unit Clause-clause subsumption calls : 43
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 545
% 0.18/0.45  # BW rewrite match successes           : 1
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 111082
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.112 s
% 0.18/0.45  # System time              : 0.005 s
% 0.18/0.45  # Total time               : 0.118 s
% 0.18/0.45  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
