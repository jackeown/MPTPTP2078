%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:19 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   34 (  72 expanded)
%              Number of clauses        :   25 (  38 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 348 expanded)
%              Number of equality atoms :   19 (  64 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t98_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_5,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
       => r1_xboole_0(k3_tarski(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t98_zfmisc_1])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    ! [X33] :
      ( ( ~ r2_hidden(X33,esk6_0)
        | r1_xboole_0(X33,esk7_0) )
      & ~ r1_xboole_0(k3_tarski(esk6_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
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

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk2_2(esk7_0,X1),X2)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk3_3(X2,k3_tarski(X2),esk2_2(esk7_0,X1)),esk6_0)
    | ~ r2_hidden(esk2_2(esk7_0,X1),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk2_2(esk7_0,X1),k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk7_0,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k3_tarski(esk6_0),X1)
    | ~ r2_hidden(esk2_2(k3_tarski(esk6_0),X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 0.40/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.40/0.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.40/0.56  #
% 0.40/0.56  # Preprocessing time       : 0.027 s
% 0.40/0.56  # Presaturation interreduction done
% 0.40/0.56  
% 0.40/0.56  # Proof found!
% 0.40/0.56  # SZS status Theorem
% 0.40/0.56  # SZS output start CNFRefutation
% 0.40/0.56  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.40/0.56  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.40/0.56  fof(t98_zfmisc_1, conjecture, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 0.40/0.56  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.40/0.56  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.40/0.56  fof(c_0_5, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.40/0.56  cnf(c_0_6, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.40/0.56  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2))), inference(assume_negation,[status(cth)],[t98_zfmisc_1])).
% 0.40/0.56  cnf(c_0_8, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.40/0.56  cnf(c_0_9, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_6])).
% 0.40/0.56  fof(c_0_10, negated_conjecture, ![X33]:((~r2_hidden(X33,esk6_0)|r1_xboole_0(X33,esk7_0))&~r1_xboole_0(k3_tarski(esk6_0),esk7_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.40/0.56  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.40/0.56  cnf(c_0_12, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.40/0.56  cnf(c_0_13, negated_conjecture, (r1_xboole_0(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.40/0.56  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 0.40/0.56  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.40/0.56  fof(c_0_16, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:((((r2_hidden(X22,esk3_3(X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k3_tarski(X20))&(r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k3_tarski(X20)))&(~r2_hidden(X24,X25)|~r2_hidden(X25,X20)|r2_hidden(X24,X21)|X21!=k3_tarski(X20)))&((~r2_hidden(esk4_2(X26,X27),X27)|(~r2_hidden(esk4_2(X26,X27),X29)|~r2_hidden(X29,X26))|X27=k3_tarski(X26))&((r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))&(r2_hidden(esk5_2(X26,X27),X26)|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.40/0.56  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.40/0.56  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.40/0.56  cnf(c_0_19, plain, (r2_hidden(X1,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.56  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r2_hidden(esk2_2(esk7_0,X1),X2)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.40/0.56  cnf(c_0_21, plain, (r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_19])).
% 0.40/0.56  cnf(c_0_22, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.56  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.40/0.56  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r2_hidden(esk3_3(X2,k3_tarski(X2),esk2_2(esk7_0,X1)),esk6_0)|~r2_hidden(esk2_2(esk7_0,X1),k3_tarski(X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.40/0.56  cnf(c_0_25, plain, (r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.40/0.56  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.40/0.56  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r2_hidden(esk2_2(esk7_0,X1),k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.40/0.56  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_26, c_0_15])).
% 0.40/0.56  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk7_0,k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.40/0.56  cnf(c_0_30, negated_conjecture, (~r2_hidden(X1,k3_tarski(esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_29])).
% 0.40/0.56  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k3_tarski(esk6_0),X1)|~r2_hidden(esk2_2(k3_tarski(esk6_0),X1),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.40/0.56  cnf(c_0_32, negated_conjecture, (~r1_xboole_0(k3_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.40/0.56  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32]), ['proof']).
% 0.40/0.56  # SZS output end CNFRefutation
% 0.40/0.56  # Proof object total steps             : 34
% 0.40/0.56  # Proof object clause steps            : 25
% 0.40/0.56  # Proof object formula steps           : 9
% 0.40/0.56  # Proof object conjectures             : 13
% 0.40/0.56  # Proof object clause conjectures      : 10
% 0.40/0.56  # Proof object formula conjectures     : 3
% 0.40/0.56  # Proof object initial clauses used    : 9
% 0.40/0.56  # Proof object initial formulas used   : 4
% 0.40/0.56  # Proof object generating inferences   : 11
% 0.40/0.56  # Proof object simplifying inferences  : 6
% 0.40/0.56  # Training examples: 0 positive, 0 negative
% 0.40/0.56  # Parsed axioms                        : 4
% 0.40/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.56  # Initial clauses                      : 16
% 0.40/0.56  # Removed in clause preprocessing      : 0
% 0.40/0.56  # Initial clauses in saturation        : 16
% 0.40/0.56  # Processed clauses                    : 1972
% 0.40/0.56  # ...of these trivial                  : 16
% 0.40/0.56  # ...subsumed                          : 1515
% 0.40/0.56  # ...remaining for further processing  : 441
% 0.40/0.56  # Other redundant clauses eliminated   : 6
% 0.40/0.56  # Clauses deleted for lack of memory   : 0
% 0.40/0.56  # Backward-subsumed                    : 10
% 0.40/0.56  # Backward-rewritten                   : 1
% 0.40/0.56  # Generated clauses                    : 13984
% 0.40/0.56  # ...of the previous two non-trivial   : 13940
% 0.40/0.56  # Contextual simplify-reflections      : 3
% 0.40/0.56  # Paramodulations                      : 13958
% 0.40/0.56  # Factorizations                       : 20
% 0.40/0.56  # Equation resolutions                 : 6
% 0.40/0.56  # Propositional unsat checks           : 0
% 0.40/0.56  #    Propositional check models        : 0
% 0.40/0.56  #    Propositional check unsatisfiable : 0
% 0.40/0.56  #    Propositional clauses             : 0
% 0.40/0.56  #    Propositional clauses after purity: 0
% 0.40/0.56  #    Propositional unsat core size     : 0
% 0.40/0.56  #    Propositional preprocessing time  : 0.000
% 0.40/0.56  #    Propositional encoding time       : 0.000
% 0.40/0.56  #    Propositional solver time         : 0.000
% 0.40/0.56  #    Success case prop preproc time    : 0.000
% 0.40/0.56  #    Success case prop encoding time   : 0.000
% 0.40/0.56  #    Success case prop solver time     : 0.000
% 0.40/0.56  # Current number of processed clauses  : 408
% 0.40/0.56  #    Positive orientable unit clauses  : 9
% 0.40/0.56  #    Positive unorientable unit clauses: 0
% 0.40/0.56  #    Negative unit clauses             : 18
% 0.40/0.56  #    Non-unit-clauses                  : 381
% 0.40/0.56  # Current number of unprocessed clauses: 11956
% 0.40/0.56  # ...number of literals in the above   : 38198
% 0.40/0.56  # Current number of archived formulas  : 0
% 0.40/0.56  # Current number of archived clauses   : 27
% 0.40/0.56  # Clause-clause subsumption calls (NU) : 16914
% 0.40/0.56  # Rec. Clause-clause subsumption calls : 10319
% 0.40/0.56  # Non-unit clause-clause subsumptions  : 599
% 0.40/0.56  # Unit Clause-clause subsumption calls : 364
% 0.40/0.56  # Rewrite failures with RHS unbound    : 0
% 0.40/0.56  # BW rewrite match attempts            : 153
% 0.40/0.56  # BW rewrite match successes           : 1
% 0.40/0.56  # Condensation attempts                : 0
% 0.40/0.56  # Condensation successes               : 0
% 0.40/0.56  # Termbank termtop insertions          : 216241
% 0.40/0.56  
% 0.40/0.56  # -------------------------------------------------
% 0.40/0.56  # User time                : 0.199 s
% 0.40/0.56  # System time              : 0.012 s
% 0.40/0.56  # Total time               : 0.211 s
% 0.40/0.56  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
