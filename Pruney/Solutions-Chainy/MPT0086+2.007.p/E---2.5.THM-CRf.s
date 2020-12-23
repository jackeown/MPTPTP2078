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
% DateTime   : Thu Dec  3 10:33:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 134 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t79_xboole_1,conjecture,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(assume_negation,[status(cth)],[t79_xboole_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ r1_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X29,X30] :
      ( ( ~ r1_xboole_0(X29,X30)
        | k3_xboole_0(X29,X30) = k1_xboole_0 )
      & ( k3_xboole_0(X29,X30) != k1_xboole_0
        | r1_xboole_0(X29,X30) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_21,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | X31 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(esk1_1(k3_xboole_0(X1,k4_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.039 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.47  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.47  fof(t79_xboole_1, conjecture, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.47  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.47  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 0.19/0.47  fof(c_0_7, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_8, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k4_xboole_0(X20,X21)))&((~r2_hidden(esk3_3(X25,X26,X27),X27)|(~r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X26))|X27=k4_xboole_0(X25,X26))&((r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))&(~r2_hidden(esk3_3(X25,X26,X27),X26)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.47  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.47  fof(c_0_10, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.47  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.47  fof(c_0_15, negated_conjecture, ~(![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(assume_negation,[status(cth)],[t79_xboole_1])).
% 0.19/0.47  cnf(c_0_16, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_17, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.47  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.47  fof(c_0_19, negated_conjecture, ~r1_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.47  fof(c_0_20, plain, ![X29, X30]:((~r1_xboole_0(X29,X30)|k3_xboole_0(X29,X30)=k1_xboole_0)&(k3_xboole_0(X29,X30)!=k1_xboole_0|r1_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.47  fof(c_0_21, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.47  fof(c_0_22, plain, ![X31]:(~v1_xboole_0(X31)|X31=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.19/0.47  cnf(c_0_23, plain, (v1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X3)))|~r2_hidden(esk1_1(k3_xboole_0(X1,k4_xboole_0(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.47  cnf(c_0_24, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X1)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.19/0.47  cnf(c_0_25, negated_conjecture, (~r1_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_29, plain, (v1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (k3_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.19/0.47  cnf(c_0_31, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 33
% 0.19/0.47  # Proof object clause steps            : 18
% 0.19/0.47  # Proof object formula steps           : 15
% 0.19/0.47  # Proof object conjectures             : 6
% 0.19/0.47  # Proof object clause conjectures      : 3
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 8
% 0.19/0.47  # Proof object initial formulas used   : 7
% 0.19/0.47  # Proof object generating inferences   : 6
% 0.19/0.47  # Proof object simplifying inferences  : 6
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 7
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 19
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 19
% 0.19/0.47  # Processed clauses                    : 760
% 0.19/0.47  # ...of these trivial                  : 8
% 0.19/0.47  # ...subsumed                          : 557
% 0.19/0.47  # ...remaining for further processing  : 195
% 0.19/0.47  # Other redundant clauses eliminated   : 6
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 4
% 0.19/0.47  # Backward-rewritten                   : 7
% 0.19/0.47  # Generated clauses                    : 4082
% 0.19/0.47  # ...of the previous two non-trivial   : 3059
% 0.19/0.47  # Contextual simplify-reflections      : 5
% 0.19/0.47  # Paramodulations                      : 4022
% 0.19/0.47  # Factorizations                       : 54
% 0.19/0.47  # Equation resolutions                 : 6
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 159
% 0.19/0.47  #    Positive orientable unit clauses  : 10
% 0.19/0.47  #    Positive unorientable unit clauses: 1
% 0.19/0.47  #    Negative unit clauses             : 3
% 0.19/0.47  #    Non-unit-clauses                  : 145
% 0.19/0.47  # Current number of unprocessed clauses: 2315
% 0.19/0.47  # ...number of literals in the above   : 7743
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 30
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 3819
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 3162
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 445
% 0.19/0.47  # Unit Clause-clause subsumption calls : 169
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 51
% 0.19/0.47  # BW rewrite match successes           : 9
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 44956
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.128 s
% 0.19/0.47  # System time              : 0.004 s
% 0.19/0.47  # Total time               : 0.132 s
% 0.19/0.47  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
