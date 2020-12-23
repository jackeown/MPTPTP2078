%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of clauses        :   20 (  25 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  126 ( 237 expanded)
%              Number of equality atoms :   41 (  64 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

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

fof(c_0_6,plain,(
    ! [X21,X22,X23,X24,X25,X27,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X23,X24)
        | X22 != k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X21,X22,X25),X21)
        | r2_hidden(X25,X22)
        | X22 != k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( ~ r2_hidden(X25,esk3_3(X21,X22,X25))
        | r2_hidden(X25,X22)
        | X22 != k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X21,X27),X21)
        | ~ r2_hidden(esk4_2(X21,X27),X27)
        | X27 = k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X21,X27),esk5_2(X21,X27))
        | ~ r2_hidden(esk4_2(X21,X27),X27)
        | X27 = k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X21,X27),X27)
        | ~ r2_hidden(X30,X21)
        | r2_hidden(esk4_2(X21,X27),X30)
        | X27 = k1_setfam_1(X21)
        | X21 = k1_xboole_0 )
      & ( X32 != k1_setfam_1(X31)
        | X32 = k1_xboole_0
        | X31 != k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | X33 = k1_setfam_1(X31)
        | X31 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => r1_tarski(k1_setfam_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t4_setfam_1])).

fof(c_0_12,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    & ~ r1_tarski(k1_setfam_1(esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14])])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk7_0),X1),esk6_0)
    | r1_tarski(k1_setfam_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2)
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_29]),c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.045 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t4_setfam_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.13/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.39  fof(c_0_6, plain, ![X21, X22, X23, X24, X25, X27, X30, X31, X32, X33]:((((~r2_hidden(X23,X22)|(~r2_hidden(X24,X21)|r2_hidden(X23,X24))|X22!=k1_setfam_1(X21)|X21=k1_xboole_0)&((r2_hidden(esk3_3(X21,X22,X25),X21)|r2_hidden(X25,X22)|X22!=k1_setfam_1(X21)|X21=k1_xboole_0)&(~r2_hidden(X25,esk3_3(X21,X22,X25))|r2_hidden(X25,X22)|X22!=k1_setfam_1(X21)|X21=k1_xboole_0)))&(((r2_hidden(esk5_2(X21,X27),X21)|~r2_hidden(esk4_2(X21,X27),X27)|X27=k1_setfam_1(X21)|X21=k1_xboole_0)&(~r2_hidden(esk4_2(X21,X27),esk5_2(X21,X27))|~r2_hidden(esk4_2(X21,X27),X27)|X27=k1_setfam_1(X21)|X21=k1_xboole_0))&(r2_hidden(esk4_2(X21,X27),X27)|(~r2_hidden(X30,X21)|r2_hidden(esk4_2(X21,X27),X30))|X27=k1_setfam_1(X21)|X21=k1_xboole_0)))&((X32!=k1_setfam_1(X31)|X32=k1_xboole_0|X31!=k1_xboole_0)&(X33!=k1_xboole_0|X33=k1_setfam_1(X31)|X31!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.39  fof(c_0_8, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.39  cnf(c_0_9, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1))), inference(assume_negation,[status(cth)],[t4_setfam_1])).
% 0.13/0.39  fof(c_0_12, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.39  cnf(c_0_13, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, (r2_hidden(esk6_0,esk7_0)&~r1_tarski(k1_setfam_1(esk7_0),esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_19, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_tarski(k1_xboole_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14])])).
% 0.13/0.39  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)|r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)|~r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk7_0),X1),esk6_0)|r1_tarski(k1_setfam_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (~r1_tarski(k1_setfam_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_26, plain, (X1=k1_xboole_0|X1!=k1_setfam_1(X2)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_27, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)|~r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.13/0.39  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.13/0.39  cnf(c_0_30, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.13/0.39  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_28])])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_29]), c_0_30]), c_0_31])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 33
% 0.13/0.39  # Proof object clause steps            : 20
% 0.13/0.39  # Proof object formula steps           : 13
% 0.13/0.39  # Proof object conjectures             : 8
% 0.13/0.39  # Proof object clause conjectures      : 5
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 9
% 0.13/0.39  # Proof object initial formulas used   : 6
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 11
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 6
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 81
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 9
% 0.13/0.39  # ...remaining for further processing  : 71
% 0.13/0.39  # Other redundant clauses eliminated   : 9
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 16
% 0.13/0.39  # Generated clauses                    : 102
% 0.13/0.39  # ...of the previous two non-trivial   : 94
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 93
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 9
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 31
% 0.13/0.39  #    Positive orientable unit clauses  : 6
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 25
% 0.13/0.39  # Current number of unprocessed clauses: 48
% 0.13/0.39  # ...number of literals in the above   : 234
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 35
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 152
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 77
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.39  # Unit Clause-clause subsumption calls : 15
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 6
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3014
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.005 s
% 0.13/0.40  # Total time               : 0.056 s
% 0.13/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
