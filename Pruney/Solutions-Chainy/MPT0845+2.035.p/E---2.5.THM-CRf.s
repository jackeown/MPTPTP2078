%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:58 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  55 expanded)
%              Number of clauses        :   17 (  25 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 196 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d5_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k3_xboole_0(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_setfam_1)).

fof(c_0_6,plain,(
    ! [X16,X17,X19] :
      ( ( r2_hidden(esk2_2(X16,X17),X17)
        | ~ r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,esk2_2(X16,X17))
        | ~ r2_hidden(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,k1_tarski(X15)) != X14
        | ~ r2_hidden(X15,X14) )
      & ( r2_hidden(X15,X14)
        | k4_xboole_0(X14,k1_tarski(X15)) = X14 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X13] : k4_xboole_0(k1_xboole_0,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_13,negated_conjecture,(
    ! [X38] :
      ( esk8_0 != k1_xboole_0
      & ( ~ r2_hidden(X38,esk8_0)
        | ~ r1_xboole_0(X38,esk8_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(esk2_2(X1,X2),X3)
    | ~ r2_hidden(esk1_2(esk2_2(X1,X2),X3),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23,X26,X27,X28,X29,X30,X31,X33,X34] :
      ( ( r2_hidden(esk3_4(X20,X21,X22,X23),X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_setfam_1(X20,X21) )
      & ( r2_hidden(esk4_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_setfam_1(X20,X21) )
      & ( X23 = k3_xboole_0(esk3_4(X20,X21,X22,X23),esk4_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k3_setfam_1(X20,X21) )
      & ( ~ r2_hidden(X27,X20)
        | ~ r2_hidden(X28,X21)
        | X26 != k3_xboole_0(X27,X28)
        | r2_hidden(X26,X22)
        | X22 != k3_setfam_1(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X29,X30,X31),X31)
        | ~ r2_hidden(X33,X29)
        | ~ r2_hidden(X34,X30)
        | esk5_3(X29,X30,X31) != k3_xboole_0(X33,X34)
        | X31 = k3_setfam_1(X29,X30) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X29)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_setfam_1(X29,X30) )
      & ( r2_hidden(esk7_3(X29,X30,X31),X30)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_setfam_1(X29,X30) )
      & ( esk5_3(X29,X30,X31) = k3_xboole_0(esk6_3(X29,X30,X31),esk7_3(X29,X30,X31))
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_setfam_1(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_setfam_1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r1_xboole_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_xboole_0(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( X1 = k3_setfam_1(k1_xboole_0,X2)
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k3_setfam_1(k1_xboole_0,X1) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,plain,
    ( X1 = esk8_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.027 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.18/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.38  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.18/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.18/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.18/0.38  fof(d5_setfam_1, axiom, ![X1, X2, X3]:(X3=k3_setfam_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k3_xboole_0(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_setfam_1)).
% 0.18/0.38  fof(c_0_6, plain, ![X16, X17, X19]:((r2_hidden(esk2_2(X16,X17),X17)|~r2_hidden(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,esk2_2(X16,X17))|~r2_hidden(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.18/0.38  fof(c_0_7, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.18/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.18/0.38  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.38  fof(c_0_11, plain, ![X14, X15]:((k4_xboole_0(X14,k1_tarski(X15))!=X14|~r2_hidden(X15,X14))&(r2_hidden(X15,X14)|k4_xboole_0(X14,k1_tarski(X15))=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.18/0.38  fof(c_0_12, plain, ![X13]:k4_xboole_0(k1_xboole_0,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.18/0.38  fof(c_0_13, negated_conjecture, ![X38]:(esk8_0!=k1_xboole_0&(~r2_hidden(X38,esk8_0)|~r1_xboole_0(X38,esk8_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.18/0.38  cnf(c_0_14, plain, (r1_xboole_0(esk2_2(X1,X2),X3)|~r2_hidden(esk1_2(esk2_2(X1,X2),X3),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.38  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.38  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_17, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  fof(c_0_18, plain, ![X20, X21, X22, X23, X26, X27, X28, X29, X30, X31, X33, X34]:(((((r2_hidden(esk3_4(X20,X21,X22,X23),X20)|~r2_hidden(X23,X22)|X22!=k3_setfam_1(X20,X21))&(r2_hidden(esk4_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k3_setfam_1(X20,X21)))&(X23=k3_xboole_0(esk3_4(X20,X21,X22,X23),esk4_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k3_setfam_1(X20,X21)))&(~r2_hidden(X27,X20)|~r2_hidden(X28,X21)|X26!=k3_xboole_0(X27,X28)|r2_hidden(X26,X22)|X22!=k3_setfam_1(X20,X21)))&((~r2_hidden(esk5_3(X29,X30,X31),X31)|(~r2_hidden(X33,X29)|~r2_hidden(X34,X30)|esk5_3(X29,X30,X31)!=k3_xboole_0(X33,X34))|X31=k3_setfam_1(X29,X30))&(((r2_hidden(esk6_3(X29,X30,X31),X29)|r2_hidden(esk5_3(X29,X30,X31),X31)|X31=k3_setfam_1(X29,X30))&(r2_hidden(esk7_3(X29,X30,X31),X30)|r2_hidden(esk5_3(X29,X30,X31),X31)|X31=k3_setfam_1(X29,X30)))&(esk5_3(X29,X30,X31)=k3_xboole_0(esk6_3(X29,X30,X31),esk7_3(X29,X30,X31))|r2_hidden(esk5_3(X29,X30,X31),X31)|X31=k3_setfam_1(X29,X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_setfam_1])])])])])])).
% 0.18/0.38  cnf(c_0_19, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r1_xboole_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_20, plain, (r1_xboole_0(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.38  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.38  cnf(c_0_23, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k3_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.18/0.38  cnf(c_0_25, plain, (X1=k3_setfam_1(k1_xboole_0,X2)|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (k3_setfam_1(k1_xboole_0,X1)=esk8_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.38  cnf(c_0_27, plain, (X1=esk8_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.38  cnf(c_0_28, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_29, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_28]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 30
% 0.18/0.38  # Proof object clause steps            : 17
% 0.18/0.38  # Proof object formula steps           : 13
% 0.18/0.38  # Proof object conjectures             : 7
% 0.18/0.38  # Proof object clause conjectures      : 4
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 9
% 0.18/0.38  # Proof object initial formulas used   : 6
% 0.18/0.38  # Proof object generating inferences   : 7
% 0.18/0.38  # Proof object simplifying inferences  : 3
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 6
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 18
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 18
% 0.18/0.38  # Processed clauses                    : 248
% 0.18/0.38  # ...of these trivial                  : 19
% 0.18/0.38  # ...subsumed                          : 108
% 0.18/0.38  # ...remaining for further processing  : 121
% 0.18/0.38  # Other redundant clauses eliminated   : 5
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 0
% 0.18/0.38  # Backward-rewritten                   : 18
% 0.18/0.38  # Generated clauses                    : 591
% 0.18/0.38  # ...of the previous two non-trivial   : 526
% 0.18/0.38  # Contextual simplify-reflections      : 1
% 0.18/0.38  # Paramodulations                      : 587
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 5
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 81
% 0.18/0.38  #    Positive orientable unit clauses  : 16
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 20
% 0.18/0.38  #    Non-unit-clauses                  : 45
% 0.18/0.38  # Current number of unprocessed clauses: 293
% 0.18/0.38  # ...number of literals in the above   : 520
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 36
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 650
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 428
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.18/0.38  # Unit Clause-clause subsumption calls : 132
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 9
% 0.18/0.38  # BW rewrite match successes           : 5
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 6331
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.039 s
% 0.18/0.38  # System time              : 0.002 s
% 0.18/0.38  # Total time               : 0.041 s
% 0.18/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
