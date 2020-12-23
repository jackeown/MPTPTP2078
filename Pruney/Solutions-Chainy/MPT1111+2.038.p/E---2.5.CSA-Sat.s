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
% DateTime   : Thu Dec  3 11:09:11 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 101 expanded)
%              Number of clauses        :   18 (  40 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 443 expanded)
%              Number of equality atoms :   31 (  94 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(t41_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( X2 != k1_struct_0(X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_4,plain,(
    ! [X11,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(esk1_1(X11),X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X14,X15)
        | ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X17,esk1_1(X11))
        | r1_xboole_0(X13,X11)
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

cnf(c_0_5,plain,
    ( r1_xboole_0(X1,X6)
    | X6 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X4,X5)
    | ~ r2_hidden(X5,esk1_1(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_6,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( X2 != k1_struct_0(X1)
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_pre_topc])).

cnf(c_0_8,plain,
    ( esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X3,esk1_1(esk1_1(X1)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X4)
    | ~ r2_hidden(X2,X5) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6]),
    [final]).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,negated_conjecture,(
    ! [X21] :
      ( l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & esk3_0 != k1_struct_0(esk2_0)
      & ( ~ m1_subset_1(X21,u1_struct_0(esk2_0))
        | ~ r2_hidden(X21,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_11,plain,
    ( esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X3,esk1_1(esk1_1(esk1_1(X1))))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_8,c_0_6]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( esk1_1(esk1_1(esk1_1(X1))) = k1_xboole_0
    | esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X3,esk1_1(esk1_1(esk1_1(esk1_1(X1)))))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_17,plain,
    ( esk1_1(esk1_1(esk1_1(esk1_1(X1)))) = k1_xboole_0
    | esk1_1(esk1_1(esk1_1(X1))) = k1_xboole_0
    | esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X2,esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_6]),
    [final]).

fof(c_0_18,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 != k1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_6]),
    [final]).

cnf(c_0_21,plain,
    ( esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1))))) = k1_xboole_0
    | esk1_1(esk1_1(esk1_1(esk1_1(X1)))) = k1_xboole_0
    | esk1_1(esk1_1(esk1_1(X1))) = k1_xboole_0
    | esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1)))))),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_6]),
    [final]).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( k1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_20]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_20]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:18:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.12/0.36  # and selection function SelectNewComplexAHPNS.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.012 s
% 0.12/0.36  
% 0.12/0.36  # No proof found!
% 0.12/0.36  # SZS status CounterSatisfiable
% 0.12/0.36  # SZS output start Saturation
% 0.12/0.36  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.12/0.36  fof(t41_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_pre_topc)).
% 0.12/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.36  fof(c_0_4, plain, ![X11, X13, X14, X15, X16, X17]:((r2_hidden(esk1_1(X11),X11)|X11=k1_xboole_0)&(~r2_hidden(X13,X14)|~r2_hidden(X14,X15)|~r2_hidden(X15,X16)|~r2_hidden(X16,X17)|~r2_hidden(X17,esk1_1(X11))|r1_xboole_0(X13,X11)|X11=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.12/0.36  cnf(c_0_5, plain, (r1_xboole_0(X1,X6)|X6=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,X4)|~r2_hidden(X4,X5)|~r2_hidden(X5,esk1_1(X6))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_6, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2)))))))), inference(assume_negation,[status(cth)],[t41_pre_topc])).
% 0.12/0.36  cnf(c_0_8, plain, (esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X3,esk1_1(esk1_1(X1)))|~r2_hidden(X4,X3)|~r2_hidden(X5,X4)|~r2_hidden(X2,X5)), inference(spm,[status(thm)],[c_0_5, c_0_6]), ['final']).
% 0.12/0.36  fof(c_0_9, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.36  fof(c_0_10, negated_conjecture, ![X21]:(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(esk3_0!=k1_struct_0(esk2_0)&(~m1_subset_1(X21,u1_struct_0(esk2_0))|~r2_hidden(X21,esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.12/0.36  cnf(c_0_11, plain, (esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X3,esk1_1(esk1_1(esk1_1(X1))))|~r2_hidden(X4,X3)|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_8, c_0_6]), ['final']).
% 0.12/0.36  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_15, plain, (esk1_1(esk1_1(esk1_1(X1)))=k1_xboole_0|esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X3,esk1_1(esk1_1(esk1_1(esk1_1(X1)))))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_11, c_0_6]), ['final']).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.12/0.36  cnf(c_0_17, plain, (esk1_1(esk1_1(esk1_1(esk1_1(X1))))=k1_xboole_0|esk1_1(esk1_1(esk1_1(X1)))=k1_xboole_0|esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X2,esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1))))))), inference(spm,[status(thm)],[c_0_15, c_0_6]), ['final']).
% 0.12/0.36  fof(c_0_18, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (esk3_0!=k1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_6]), ['final']).
% 0.12/0.36  cnf(c_0_21, plain, (esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1)))))=k1_xboole_0|esk1_1(esk1_1(esk1_1(esk1_1(X1))))=k1_xboole_0|esk1_1(esk1_1(esk1_1(X1)))=k1_xboole_0|esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(esk1_1(X1)))))),X1)), inference(spm,[status(thm)],[c_0_17, c_0_6]), ['final']).
% 0.12/0.36  cnf(c_0_22, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (k1_struct_0(esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_16, c_0_20]), ['final']).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_13, c_0_20]), ['final']).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.12/0.36  # SZS output end Saturation
% 0.12/0.36  # Proof object total steps             : 27
% 0.12/0.36  # Proof object clause steps            : 18
% 0.12/0.36  # Proof object formula steps           : 9
% 0.12/0.36  # Proof object conjectures             : 12
% 0.12/0.36  # Proof object clause conjectures      : 9
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 8
% 0.12/0.36  # Proof object initial formulas used   : 4
% 0.12/0.36  # Proof object generating inferences   : 7
% 0.12/0.36  # Proof object simplifying inferences  : 4
% 0.12/0.36  # Parsed axioms                        : 4
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 8
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 8
% 0.12/0.36  # Processed clauses                    : 21
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 2
% 0.12/0.36  # ...remaining for further processing  : 19
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 5
% 0.12/0.36  # Generated clauses                    : 9
% 0.12/0.36  # ...of the previous two non-trivial   : 13
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 9
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 14
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 9
% 0.12/0.36  # Current number of unprocessed clauses: 0
% 0.12/0.36  # ...number of literals in the above   : 0
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 5
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 12
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 1
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.36  # Unit Clause-clause subsumption calls : 3
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1014
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.014 s
% 0.12/0.36  # System time              : 0.002 s
% 0.12/0.36  # Total time               : 0.016 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
