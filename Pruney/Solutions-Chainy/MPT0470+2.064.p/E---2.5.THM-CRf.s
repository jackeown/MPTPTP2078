%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  70 expanded)
%              Number of clauses        :   17 (  30 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 229 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_7,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_9,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X19,X20,X22,X23,X24,X27] :
      ( ( r2_hidden(k4_tarski(X19,esk2_5(X16,X17,X18,X19,X20)),X16)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk2_5(X16,X17,X18,X19,X20),X20),X17)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X22,X24),X16)
        | ~ r2_hidden(k4_tarski(X24,X23),X17)
        | r2_hidden(k4_tarski(X22,X23),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)
        | ~ r2_hidden(k4_tarski(esk3_3(X16,X17,X18),X27),X16)
        | ~ r2_hidden(k4_tarski(X27,esk4_3(X16,X17,X18)),X17)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk5_3(X16,X17,X18)),X16)
        | r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk5_3(X16,X17,X18),esk4_3(X16,X17,X18)),X17)
        | r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( k5_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0
      | k5_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( X1 = k5_relat_1(X2,k1_xboole_0)
    | r2_hidden(k4_tarski(esk3_3(X2,k1_xboole_0,X1),esk4_3(X2,k1_xboole_0,X1)),X1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0
    | k5_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk3_3(k1_xboole_0,X2,X1),esk4_3(k1_xboole_0,X2,X1)),X1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

fof(c_0_26,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.21/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.041 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.44  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.44  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.21/0.44  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.21/0.44  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.21/0.44  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.21/0.44  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.44  fof(c_0_7, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.44  fof(c_0_8, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.44  fof(c_0_9, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.21/0.44  cnf(c_0_10, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.44  cnf(c_0_11, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.44  cnf(c_0_12, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.44  fof(c_0_13, plain, ![X16, X17, X18, X19, X20, X22, X23, X24, X27]:((((r2_hidden(k4_tarski(X19,esk2_5(X16,X17,X18,X19,X20)),X16)|~r2_hidden(k4_tarski(X19,X20),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk2_5(X16,X17,X18,X19,X20),X20),X17)|~r2_hidden(k4_tarski(X19,X20),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(X22,X24),X16)|~r2_hidden(k4_tarski(X24,X23),X17)|r2_hidden(k4_tarski(X22,X23),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)|(~r2_hidden(k4_tarski(esk3_3(X16,X17,X18),X27),X16)|~r2_hidden(k4_tarski(X27,esk4_3(X16,X17,X18)),X17))|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk5_3(X16,X17,X18)),X16)|r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk5_3(X16,X17,X18),esk4_3(X16,X17,X18)),X17)|r2_hidden(k4_tarski(esk3_3(X16,X17,X18),esk4_3(X16,X17,X18)),X18)|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.21/0.44  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.21/0.44  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.21/0.44  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.44  fof(c_0_17, negated_conjecture, (v1_relat_1(esk6_0)&(k5_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0|k5_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.44  cnf(c_0_18, plain, (X1=k5_relat_1(X2,k1_xboole_0)|r2_hidden(k4_tarski(esk3_3(X2,k1_xboole_0,X1),esk4_3(X2,k1_xboole_0,X1)),X1)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.44  cnf(c_0_19, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.44  cnf(c_0_20, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0|k5_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_21, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_18])).
% 0.21/0.44  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_23, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk3_3(k1_xboole_0,X2,X1),esk4_3(k1_xboole_0,X2,X1)),X1)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 0.21/0.44  cnf(c_0_24, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.21/0.44  cnf(c_0_25, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.21/0.44  fof(c_0_26, plain, ![X15]:(~v1_xboole_0(X15)|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.21/0.44  cnf(c_0_27, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_22])])).
% 0.21/0.44  cnf(c_0_28, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.44  cnf(c_0_29, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.44  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 31
% 0.21/0.44  # Proof object clause steps            : 17
% 0.21/0.44  # Proof object formula steps           : 14
% 0.21/0.44  # Proof object conjectures             : 8
% 0.21/0.44  # Proof object clause conjectures      : 5
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 9
% 0.21/0.44  # Proof object initial formulas used   : 7
% 0.21/0.44  # Proof object generating inferences   : 8
% 0.21/0.44  # Proof object simplifying inferences  : 8
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 7
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 14
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 14
% 0.21/0.44  # Processed clauses                    : 186
% 0.21/0.44  # ...of these trivial                  : 0
% 0.21/0.44  # ...subsumed                          : 66
% 0.21/0.44  # ...remaining for further processing  : 120
% 0.21/0.44  # Other redundant clauses eliminated   : 0
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 11
% 0.21/0.44  # Backward-rewritten                   : 0
% 0.21/0.44  # Generated clauses                    : 389
% 0.21/0.44  # ...of the previous two non-trivial   : 386
% 0.21/0.44  # Contextual simplify-reflections      : 0
% 0.21/0.44  # Paramodulations                      : 367
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 22
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 95
% 0.21/0.44  #    Positive orientable unit clauses  : 4
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 2
% 0.21/0.44  #    Non-unit-clauses                  : 89
% 0.21/0.44  # Current number of unprocessed clauses: 224
% 0.21/0.44  # ...number of literals in the above   : 2237
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 25
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 6484
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 943
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 72
% 0.21/0.44  # Unit Clause-clause subsumption calls : 71
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 0
% 0.21/0.44  # BW rewrite match successes           : 0
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 11909
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.080 s
% 0.21/0.44  # System time              : 0.006 s
% 0.21/0.44  # Total time               : 0.087 s
% 0.21/0.44  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
