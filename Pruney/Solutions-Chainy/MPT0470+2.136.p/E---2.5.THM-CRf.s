%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:14 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 161 expanded)
%              Number of clauses        :   24 (  72 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 424 expanded)
%              Number of equality atoms :   30 ( 106 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | v1_relat_1(k3_xboole_0(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_10,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_12,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
      | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_16,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X21] : r1_xboole_0(X21,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27,X28,X30,X31,X32,X35] :
      ( ( r2_hidden(k4_tarski(X27,esk3_5(X24,X25,X26,X27,X28)),X24)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk3_5(X24,X25,X26,X27,X28),X28),X25)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X30,X32),X24)
        | ~ r2_hidden(k4_tarski(X32,X31),X25)
        | r2_hidden(k4_tarski(X30,X31),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | ~ r2_hidden(k4_tarski(esk4_3(X24,X25,X26),X35),X24)
        | ~ r2_hidden(k4_tarski(X35,esk5_3(X24,X25,X26)),X25)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk6_3(X24,X25,X26)),X24)
        | r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk5_3(X24,X25,X26)),X25)
        | r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k2_tarski(esk9_0,X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k5_relat_1(X2,esk9_0)
    | r2_hidden(k4_tarski(esk4_3(X2,esk9_0,X1),esk6_3(X2,esk9_0,X1)),X2)
    | r2_hidden(k4_tarski(esk4_3(X2,esk9_0,X1),esk5_3(X2,esk9_0,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(X1,esk9_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_3(X1,esk9_0,k1_xboole_0),esk6_3(X1,esk9_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k5_relat_1(esk9_0,X2)
    | r2_hidden(k4_tarski(esk6_3(esk9_0,X2,X1),esk5_3(esk9_0,X2,X1)),X2)
    | r2_hidden(k4_tarski(esk4_3(esk9_0,X2,X1),esk5_3(esk9_0,X2,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k5_relat_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(esk9_0,X1,k1_xboole_0),esk5_3(esk9_0,X1,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_41]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.84/1.07  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.84/1.07  # and selection function SelectNegativeLiterals.
% 0.84/1.07  #
% 0.84/1.07  # Preprocessing time       : 0.029 s
% 0.84/1.07  # Presaturation interreduction done
% 0.84/1.07  
% 0.84/1.07  # Proof found!
% 0.84/1.07  # SZS status Theorem
% 0.84/1.07  # SZS output start CNFRefutation
% 0.84/1.07  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.84/1.07  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.84/1.07  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.84/1.07  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.84/1.07  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.84/1.07  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.84/1.07  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.84/1.07  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.84/1.07  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.84/1.07  fof(c_0_9, plain, ![X39, X40]:(~v1_relat_1(X39)|v1_relat_1(k3_xboole_0(X39,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.84/1.07  fof(c_0_10, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.84/1.07  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.84/1.07  cnf(c_0_12, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.84/1.07  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.84/1.07  fof(c_0_14, negated_conjecture, (v1_relat_1(esk9_0)&(k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.84/1.07  fof(c_0_15, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.84/1.07  fof(c_0_16, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk2_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk2_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.84/1.07  fof(c_0_17, plain, ![X21]:r1_xboole_0(X21,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.84/1.07  fof(c_0_18, plain, ![X24, X25, X26, X27, X28, X30, X31, X32, X35]:((((r2_hidden(k4_tarski(X27,esk3_5(X24,X25,X26,X27,X28)),X24)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk3_5(X24,X25,X26,X27,X28),X28),X25)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&(~r2_hidden(k4_tarski(X30,X32),X24)|~r2_hidden(k4_tarski(X32,X31),X25)|r2_hidden(k4_tarski(X30,X31),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&((~r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|(~r2_hidden(k4_tarski(esk4_3(X24,X25,X26),X35),X24)|~r2_hidden(k4_tarski(X35,esk5_3(X24,X25,X26)),X25))|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&((r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk6_3(X24,X25,X26)),X24)|r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk5_3(X24,X25,X26)),X25)|r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.84/1.07  cnf(c_0_19, plain, (v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.84/1.07  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.84/1.07  cnf(c_0_21, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.84/1.07  fof(c_0_22, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.84/1.07  fof(c_0_23, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.84/1.07  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.07  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.07  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.84/1.07  cnf(c_0_27, negated_conjecture, (v1_relat_1(k1_setfam_1(k2_tarski(esk9_0,X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.84/1.07  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_13])).
% 0.84/1.07  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.84/1.07  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.07  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.84/1.07  cnf(c_0_32, negated_conjecture, (X1=k5_relat_1(X2,esk9_0)|r2_hidden(k4_tarski(esk4_3(X2,esk9_0,X1),esk6_3(X2,esk9_0,X1)),X2)|r2_hidden(k4_tarski(esk4_3(X2,esk9_0,X1),esk5_3(X2,esk9_0,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.84/1.07  cnf(c_0_33, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.84/1.07  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.84/1.07  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.84/1.07  cnf(c_0_36, negated_conjecture, (k5_relat_1(X1,esk9_0)=k1_xboole_0|r2_hidden(k4_tarski(esk4_3(X1,esk9_0,k1_xboole_0),esk6_3(X1,esk9_0,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.84/1.07  cnf(c_0_37, negated_conjecture, (X1=k5_relat_1(esk9_0,X2)|r2_hidden(k4_tarski(esk6_3(esk9_0,X2,X1),esk5_3(esk9_0,X2,X1)),X2)|r2_hidden(k4_tarski(esk4_3(esk9_0,X2,X1),esk5_3(esk9_0,X2,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.84/1.07  cnf(c_0_38, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.84/1.07  cnf(c_0_39, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_34])).
% 0.84/1.07  cnf(c_0_40, negated_conjecture, (k5_relat_1(esk9_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(esk9_0,X1,k1_xboole_0),esk5_3(esk9_0,X1,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34])).
% 0.84/1.07  cnf(c_0_41, negated_conjecture, (k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.84/1.07  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_41]), c_0_34]), ['proof']).
% 0.84/1.07  # SZS output end CNFRefutation
% 0.84/1.07  # Proof object total steps             : 43
% 0.84/1.07  # Proof object clause steps            : 24
% 0.84/1.07  # Proof object formula steps           : 19
% 0.84/1.07  # Proof object conjectures             : 14
% 0.84/1.07  # Proof object clause conjectures      : 11
% 0.84/1.07  # Proof object formula conjectures     : 3
% 0.84/1.07  # Proof object initial clauses used    : 11
% 0.84/1.07  # Proof object initial formulas used   : 9
% 0.84/1.07  # Proof object generating inferences   : 10
% 0.84/1.07  # Proof object simplifying inferences  : 10
% 0.84/1.07  # Training examples: 0 positive, 0 negative
% 0.84/1.07  # Parsed axioms                        : 11
% 0.84/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.84/1.07  # Initial clauses                      : 21
% 0.84/1.07  # Removed in clause preprocessing      : 1
% 0.84/1.07  # Initial clauses in saturation        : 20
% 0.84/1.07  # Processed clauses                    : 804
% 0.84/1.07  # ...of these trivial                  : 77
% 0.84/1.07  # ...subsumed                          : 103
% 0.84/1.07  # ...remaining for further processing  : 624
% 0.84/1.07  # Other redundant clauses eliminated   : 3
% 0.84/1.07  # Clauses deleted for lack of memory   : 0
% 0.84/1.07  # Backward-subsumed                    : 0
% 0.84/1.07  # Backward-rewritten                   : 138
% 0.84/1.07  # Generated clauses                    : 61489
% 0.84/1.07  # ...of the previous two non-trivial   : 60304
% 0.84/1.07  # Contextual simplify-reflections      : 6
% 0.84/1.07  # Paramodulations                      : 61485
% 0.84/1.07  # Factorizations                       : 0
% 0.84/1.07  # Equation resolutions                 : 3
% 0.84/1.07  # Propositional unsat checks           : 0
% 0.84/1.07  #    Propositional check models        : 0
% 0.84/1.07  #    Propositional check unsatisfiable : 0
% 0.84/1.07  #    Propositional clauses             : 0
% 0.84/1.07  #    Propositional clauses after purity: 0
% 0.84/1.07  #    Propositional unsat core size     : 0
% 0.84/1.07  #    Propositional preprocessing time  : 0.000
% 0.84/1.07  #    Propositional encoding time       : 0.000
% 0.84/1.07  #    Propositional solver time         : 0.000
% 0.84/1.07  #    Success case prop preproc time    : 0.000
% 0.84/1.07  #    Success case prop encoding time   : 0.000
% 0.84/1.07  #    Success case prop solver time     : 0.000
% 0.84/1.07  # Current number of processed clauses  : 462
% 0.84/1.07  #    Positive orientable unit clauses  : 236
% 0.84/1.07  #    Positive unorientable unit clauses: 0
% 0.84/1.07  #    Negative unit clauses             : 2
% 0.84/1.07  #    Non-unit-clauses                  : 224
% 0.84/1.07  # Current number of unprocessed clauses: 59279
% 0.84/1.07  # ...number of literals in the above   : 135378
% 0.84/1.07  # Current number of archived formulas  : 0
% 0.84/1.07  # Current number of archived clauses   : 160
% 0.84/1.07  # Clause-clause subsumption calls (NU) : 15342
% 0.84/1.07  # Rec. Clause-clause subsumption calls : 5128
% 0.84/1.07  # Non-unit clause-clause subsumptions  : 90
% 0.84/1.07  # Unit Clause-clause subsumption calls : 1311
% 0.84/1.07  # Rewrite failures with RHS unbound    : 0
% 0.84/1.07  # BW rewrite match attempts            : 13373
% 0.84/1.07  # BW rewrite match successes           : 4
% 0.84/1.07  # Condensation attempts                : 0
% 0.84/1.07  # Condensation successes               : 0
% 0.84/1.07  # Termbank termtop insertions          : 2760674
% 0.84/1.07  
% 0.84/1.07  # -------------------------------------------------
% 0.84/1.07  # User time                : 0.668 s
% 0.84/1.07  # System time              : 0.059 s
% 0.84/1.07  # Total time               : 0.726 s
% 0.84/1.07  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
