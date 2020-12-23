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
% DateTime   : Thu Dec  3 10:49:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 225 expanded)
%              Number of clauses        :   22 ( 110 expanded)
%              Number of leaves         :    5 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 826 expanded)
%              Number of equality atoms :   29 ( 146 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X11,X12,X15,X17,X18] :
      ( ( ~ v1_relat_1(X11)
        | ~ r2_hidden(X12,X11)
        | X12 = k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)) )
      & ( r2_hidden(esk4_1(X15),X15)
        | v1_relat_1(X15) )
      & ( esk4_1(X15) != k4_tarski(X17,X18)
        | v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X27,X30] :
      ( ( r2_hidden(k4_tarski(X22,esk5_5(X19,X20,X21,X22,X23)),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_5(X19,X20,X21,X22,X23),X23),X20)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X25,X27),X19)
        | ~ r2_hidden(k4_tarski(X27,X26),X20)
        | r2_hidden(k4_tarski(X25,X26),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)
        | ~ r2_hidden(k4_tarski(esk6_3(X19,X20,X21),X30),X19)
        | ~ r2_hidden(k4_tarski(X30,esk7_3(X19,X20,X21)),X20)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk8_3(X19,X20,X21)),X19)
        | r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk8_3(X19,X20,X21),esk7_3(X19,X20,X21)),X20)
        | r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk8_3(X1,X2,X3),esk7_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_15,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk8_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
      | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_17,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk8_3(X1,k1_xboole_0,k1_xboole_0),esk7_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk6_3(X1,k1_xboole_0,k1_xboole_0),esk7_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk8_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_20]),c_0_11])])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk8_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_21]),c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_22]),c_0_11])])).

cnf(c_0_26,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk8_3(X1,X2,k1_xboole_0)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_18]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(X1,esk9_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk9_0,k1_xboole_0),esk8_3(X1,esk9_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_13]),c_0_30]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.39  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.39  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.19/0.39  fof(c_0_5, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_6, plain, ![X11, X12, X15, X17, X18]:((~v1_relat_1(X11)|(~r2_hidden(X12,X11)|X12=k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12))))&((r2_hidden(esk4_1(X15),X15)|v1_relat_1(X15))&(esk4_1(X15)!=k4_tarski(X17,X18)|v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.39  cnf(c_0_7, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_8, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  fof(c_0_9, plain, ![X19, X20, X21, X22, X23, X25, X26, X27, X30]:((((r2_hidden(k4_tarski(X22,esk5_5(X19,X20,X21,X22,X23)),X19)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk5_5(X19,X20,X21,X22,X23),X23),X20)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(X25,X27),X19)|~r2_hidden(k4_tarski(X27,X26),X20)|r2_hidden(k4_tarski(X25,X26),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&((~r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)|(~r2_hidden(k4_tarski(esk6_3(X19,X20,X21),X30),X19)|~r2_hidden(k4_tarski(X30,esk7_3(X19,X20,X21)),X20))|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&((r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk8_3(X19,X20,X21)),X19)|r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk8_3(X19,X20,X21),esk7_3(X19,X20,X21)),X20)|r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk7_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.39  cnf(c_0_10, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.39  cnf(c_0_11, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  cnf(c_0_12, plain, (r2_hidden(k4_tarski(esk8_3(X1,X2,X3),esk7_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_13, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.19/0.39  cnf(c_0_15, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk8_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.39  fof(c_0_16, negated_conjecture, (v1_relat_1(esk9_0)&(k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.39  cnf(c_0_17, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|r2_hidden(k4_tarski(esk8_3(X1,k1_xboole_0,k1_xboole_0),esk7_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk6_3(X1,k1_xboole_0,k1_xboole_0),esk7_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_19, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (k5_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk8_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (k5_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(esk9_0,k1_xboole_0,k1_xboole_0),esk7_3(esk9_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_20]), c_0_11])])).
% 0.19/0.39  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk8_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_24, plain, (~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_21]), c_0_10])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (k5_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_22]), c_0_11])])).
% 0.19/0.39  cnf(c_0_26, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk8_3(X1,X2,k1_xboole_0)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13]), c_0_18]), c_0_11])])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k5_relat_1(X1,esk9_0)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,esk9_0,k1_xboole_0),esk8_3(X1,esk9_0,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_27])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25])])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_13]), c_0_30]), c_0_27]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 32
% 0.19/0.39  # Proof object clause steps            : 22
% 0.19/0.39  # Proof object formula steps           : 10
% 0.19/0.39  # Proof object conjectures             : 12
% 0.19/0.39  # Proof object clause conjectures      : 9
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 8
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 12
% 0.19/0.39  # Proof object simplifying inferences  : 15
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 5
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 14
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 14
% 0.19/0.39  # Processed clauses                    : 205
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 72
% 0.19/0.39  # ...remaining for further processing  : 133
% 0.19/0.39  # Other redundant clauses eliminated   : 4
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 16
% 0.19/0.39  # Backward-rewritten                   : 13
% 0.19/0.39  # Generated clauses                    : 296
% 0.19/0.39  # ...of the previous two non-trivial   : 276
% 0.19/0.39  # Contextual simplify-reflections      : 6
% 0.19/0.39  # Paramodulations                      : 290
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 4
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 85
% 0.19/0.39  #    Positive orientable unit clauses  : 6
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 76
% 0.19/0.39  # Current number of unprocessed clauses: 96
% 0.19/0.39  # ...number of literals in the above   : 764
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 45
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 3238
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1203
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 71
% 0.19/0.39  # Unit Clause-clause subsumption calls : 134
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 6
% 0.19/0.39  # BW rewrite match successes           : 2
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10088
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.047 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.051 s
% 0.19/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
