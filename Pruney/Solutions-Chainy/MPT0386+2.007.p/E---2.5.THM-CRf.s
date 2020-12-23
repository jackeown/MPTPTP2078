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
% DateTime   : Thu Dec  3 10:47:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  71 expanded)
%              Number of clauses        :   23 (  33 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 219 expanded)
%              Number of equality atoms :   46 (  68 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t4_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_7,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_8,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11])])).

fof(c_0_21,plain,(
    ! [X25,X26,X27,X28,X29,X31,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X27,X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X27,X28)
        | X26 != k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X25,X26,X29),X25)
        | r2_hidden(X29,X26)
        | X26 != k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( ~ r2_hidden(X29,esk3_3(X25,X26,X29))
        | r2_hidden(X29,X26)
        | X26 != k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X25,X31),X25)
        | ~ r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X25,X31),esk5_2(X25,X31))
        | ~ r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X25,X31),X31)
        | ~ r2_hidden(X34,X25)
        | r2_hidden(esk4_2(X25,X31),X34)
        | X31 = k1_setfam_1(X25)
        | X25 = k1_xboole_0 )
      & ( X36 != k1_setfam_1(X35)
        | X36 = k1_xboole_0
        | X35 != k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | X37 = k1_setfam_1(X35)
        | X35 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => r1_tarski(k1_setfam_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t4_setfam_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    & ~ r1_tarski(k1_setfam_1(esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(X4)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | X2 != k1_setfam_1(esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_setfam_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(k1_setfam_1(esk7_0),X1),esk6_0)
    | r1_tarski(k1_setfam_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.37  fof(t4_setfam_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.13/0.37  fof(c_0_7, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.37  fof(c_0_9, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.37  cnf(c_0_10, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.37  fof(c_0_14, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.37  cnf(c_0_15, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_10, c_0_15])).
% 0.13/0.37  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_11])])).
% 0.13/0.37  fof(c_0_21, plain, ![X25, X26, X27, X28, X29, X31, X34, X35, X36, X37]:((((~r2_hidden(X27,X26)|(~r2_hidden(X28,X25)|r2_hidden(X27,X28))|X26!=k1_setfam_1(X25)|X25=k1_xboole_0)&((r2_hidden(esk3_3(X25,X26,X29),X25)|r2_hidden(X29,X26)|X26!=k1_setfam_1(X25)|X25=k1_xboole_0)&(~r2_hidden(X29,esk3_3(X25,X26,X29))|r2_hidden(X29,X26)|X26!=k1_setfam_1(X25)|X25=k1_xboole_0)))&(((r2_hidden(esk5_2(X25,X31),X25)|~r2_hidden(esk4_2(X25,X31),X31)|X31=k1_setfam_1(X25)|X25=k1_xboole_0)&(~r2_hidden(esk4_2(X25,X31),esk5_2(X25,X31))|~r2_hidden(esk4_2(X25,X31),X31)|X31=k1_setfam_1(X25)|X25=k1_xboole_0))&(r2_hidden(esk4_2(X25,X31),X31)|(~r2_hidden(X34,X25)|r2_hidden(esk4_2(X25,X31),X34))|X31=k1_setfam_1(X25)|X25=k1_xboole_0)))&((X36!=k1_setfam_1(X35)|X36=k1_xboole_0|X35!=k1_xboole_0)&(X37!=k1_xboole_0|X37=k1_setfam_1(X35)|X35!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_23, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.13/0.37  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_20])).
% 0.13/0.37  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1))), inference(assume_negation,[status(cth)],[t4_setfam_1])).
% 0.13/0.37  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_27, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.37  fof(c_0_28, negated_conjecture, (r2_hidden(esk6_0,esk7_0)&~r1_tarski(k1_setfam_1(esk7_0),esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(X4)|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk6_0)|X2!=k1_setfam_1(esk7_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_setfam_1(esk7_0))), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(k1_setfam_1(esk7_0),X1),esk6_0)|r1_tarski(k1_setfam_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~r1_tarski(k1_setfam_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 38
% 0.13/0.37  # Proof object clause steps            : 23
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 9
% 0.13/0.37  # Proof object clause conjectures      : 6
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 5
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 7
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 23
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 23
% 0.13/0.37  # Processed clauses                    : 89
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 24
% 0.13/0.37  # ...remaining for further processing  : 63
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 86
% 0.13/0.37  # ...of the previous two non-trivial   : 60
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 79
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 7
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 37
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 24
% 0.13/0.37  # Current number of unprocessed clauses: 14
% 0.13/0.37  # ...number of literals in the above   : 47
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 26
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 86
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 56
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.37  # Unit Clause-clause subsumption calls : 11
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 10
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2264
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
