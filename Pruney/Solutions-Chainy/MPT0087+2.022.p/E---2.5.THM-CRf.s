%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:37 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 236 expanded)
%              Number of clauses        :   38 ( 114 expanded)
%              Number of leaves         :    6 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 815 expanded)
%              Number of equality atoms :    7 (  28 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t80_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(c_0_6,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17] :
      ( ( r1_xboole_0(X15,k2_xboole_0(X16,X17))
        | ~ r1_xboole_0(X15,X16)
        | ~ r1_xboole_0(X15,X17) )
      & ( r1_xboole_0(X15,X16)
        | ~ r1_xboole_0(X15,k2_xboole_0(X16,X17)) )
      & ( r1_xboole_0(X15,X17)
        | ~ r1_xboole_0(X15,k2_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_8,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_18,plain,(
    ! [X18,X19] : r1_xboole_0(k4_xboole_0(X18,X19),X19) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,k4_xboole_0(X2,X1))
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_27])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X1),X2)
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_31])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X1),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_34])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t80_xboole_1])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X2))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_37])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X4)
    | ~ r1_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X1)))
    | ~ r1_xboole_0(X4,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_38])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

fof(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:41:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 0.18/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.049 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.52  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.18/0.52  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.52  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.18/0.52  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.52  fof(t80_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 0.18/0.52  fof(c_0_6, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.18/0.52  fof(c_0_7, plain, ![X15, X16, X17]:((r1_xboole_0(X15,k2_xboole_0(X16,X17))|~r1_xboole_0(X15,X16)|~r1_xboole_0(X15,X17))&((r1_xboole_0(X15,X16)|~r1_xboole_0(X15,k2_xboole_0(X16,X17)))&(r1_xboole_0(X15,X17)|~r1_xboole_0(X15,k2_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.18/0.52  fof(c_0_8, plain, ![X10, X11]:k2_xboole_0(X10,k4_xboole_0(X11,X10))=k2_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.52  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.52  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.52  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.52  cnf(c_0_12, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.52  cnf(c_0_13, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.52  cnf(c_0_14, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.52  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_11])).
% 0.18/0.52  cnf(c_0_16, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.52  cnf(c_0_17, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.52  fof(c_0_18, plain, ![X18, X19]:r1_xboole_0(k4_xboole_0(X18,X19),X19), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.18/0.52  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_11])).
% 0.18/0.52  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 0.18/0.52  cnf(c_0_21, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.52  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_23, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,X2)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.18/0.52  cnf(c_0_24, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.18/0.52  cnf(c_0_25, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,k4_xboole_0(X2,X1))|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 0.18/0.52  cnf(c_0_26, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.18/0.52  cnf(c_0_27, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 0.18/0.52  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.52  cnf(c_0_29, plain, (r1_xboole_0(k2_xboole_0(X1,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.52  fof(c_0_30, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.52  cnf(c_0_31, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_13])).
% 0.18/0.52  cnf(c_0_32, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_12, c_0_27])).
% 0.18/0.52  cnf(c_0_33, plain, (r1_xboole_0(k2_xboole_0(X1,X1),X2)|~r1_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.52  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.52  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_31])).
% 0.18/0.52  cnf(c_0_36, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2))))), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.18/0.52  cnf(c_0_37, plain, (r1_xboole_0(k2_xboole_0(X1,X1),X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.18/0.52  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_34])).
% 0.18/0.52  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t80_xboole_1])).
% 0.18/0.52  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.52  cnf(c_0_41, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X2))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_37])).
% 0.18/0.52  cnf(c_0_42, plain, (r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X4)|~r1_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X1)))|~r1_xboole_0(X4,X1)), inference(spm,[status(thm)],[c_0_23, c_0_38])).
% 0.18/0.52  cnf(c_0_43, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.18/0.52  fof(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)&~r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.18/0.52  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.52  cnf(c_0_46, plain, (r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.52  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.52  cnf(c_0_48, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.52  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.52  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 51
% 0.18/0.52  # Proof object clause steps            : 38
% 0.18/0.52  # Proof object formula steps           : 13
% 0.18/0.52  # Proof object conjectures             : 6
% 0.18/0.52  # Proof object clause conjectures      : 3
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 11
% 0.18/0.52  # Proof object initial formulas used   : 6
% 0.18/0.52  # Proof object generating inferences   : 27
% 0.18/0.52  # Proof object simplifying inferences  : 4
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.52  # Parsed axioms                        : 6
% 0.18/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.52  # Initial clauses                      : 11
% 0.18/0.52  # Removed in clause preprocessing      : 0
% 0.18/0.52  # Initial clauses in saturation        : 11
% 0.18/0.52  # Processed clauses                    : 1373
% 0.18/0.52  # ...of these trivial                  : 147
% 0.18/0.52  # ...subsumed                          : 945
% 0.18/0.52  # ...remaining for further processing  : 281
% 0.18/0.52  # Other redundant clauses eliminated   : 0
% 0.18/0.52  # Clauses deleted for lack of memory   : 0
% 0.18/0.52  # Backward-subsumed                    : 6
% 0.18/0.52  # Backward-rewritten                   : 12
% 0.18/0.52  # Generated clauses                    : 10283
% 0.18/0.52  # ...of the previous two non-trivial   : 7974
% 0.18/0.52  # Contextual simplify-reflections      : 2
% 0.18/0.52  # Paramodulations                      : 10283
% 0.18/0.52  # Factorizations                       : 0
% 0.18/0.52  # Equation resolutions                 : 0
% 0.18/0.52  # Propositional unsat checks           : 0
% 0.18/0.52  #    Propositional check models        : 0
% 0.18/0.52  #    Propositional check unsatisfiable : 0
% 0.18/0.52  #    Propositional clauses             : 0
% 0.18/0.52  #    Propositional clauses after purity: 0
% 0.18/0.52  #    Propositional unsat core size     : 0
% 0.18/0.52  #    Propositional preprocessing time  : 0.000
% 0.18/0.52  #    Propositional encoding time       : 0.000
% 0.18/0.52  #    Propositional solver time         : 0.000
% 0.18/0.52  #    Success case prop preproc time    : 0.000
% 0.18/0.52  #    Success case prop encoding time   : 0.000
% 0.18/0.52  #    Success case prop solver time     : 0.000
% 0.18/0.52  # Current number of processed clauses  : 252
% 0.18/0.52  #    Positive orientable unit clauses  : 107
% 0.18/0.52  #    Positive unorientable unit clauses: 0
% 0.18/0.52  #    Negative unit clauses             : 2
% 0.18/0.52  #    Non-unit-clauses                  : 143
% 0.18/0.52  # Current number of unprocessed clauses: 6597
% 0.18/0.52  # ...number of literals in the above   : 10847
% 0.18/0.52  # Current number of archived formulas  : 0
% 0.18/0.52  # Current number of archived clauses   : 29
% 0.18/0.52  # Clause-clause subsumption calls (NU) : 20669
% 0.18/0.52  # Rec. Clause-clause subsumption calls : 20669
% 0.18/0.52  # Non-unit clause-clause subsumptions  : 953
% 0.18/0.52  # Unit Clause-clause subsumption calls : 12
% 0.18/0.52  # Rewrite failures with RHS unbound    : 0
% 0.18/0.52  # BW rewrite match attempts            : 1335
% 0.18/0.52  # BW rewrite match successes           : 12
% 0.18/0.52  # Condensation attempts                : 0
% 0.18/0.52  # Condensation successes               : 0
% 0.18/0.52  # Termbank termtop insertions          : 129500
% 0.18/0.52  
% 0.18/0.52  # -------------------------------------------------
% 0.18/0.52  # User time                : 0.189 s
% 0.18/0.52  # System time              : 0.010 s
% 0.18/0.52  # Total time               : 0.199 s
% 0.18/0.52  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
