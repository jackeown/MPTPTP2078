%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:07 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 461 expanded)
%              Number of clauses        :   37 ( 216 expanded)
%              Number of leaves         :    7 ( 118 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 (1459 expanded)
%              Number of equality atoms :   17 ( 169 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_7,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( X2 != k1_struct_0(X1)
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_pre_topc])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X22] :
      ( l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & esk4_0 != k1_struct_0(esk3_0)
      & ( ~ m1_subset_1(X22,u1_struct_0(esk3_0))
        | ~ r2_hidden(X22,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_17,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0]),
    [final]).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_27]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 != k1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,X1)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( X1 != esk4_0
    | ~ v1_xboole_0(k1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_34,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_35,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,X1)
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(k1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27]),c_0_25]),
    [final]).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(X3,X1)
    | ~ v1_xboole_0(esk2_2(X1,X2))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_29]),
    [final]).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29]),
    [final]).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(esk1_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29]),
    [final]).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(esk2_2(X1,X2))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29]),
    [final]).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22]),
    [final]).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22]),
    [final]).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_27]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( k1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_27]),
    [final]).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.37  # and selection function SelectNewComplexAHP.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(t41_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_pre_topc)).
% 0.20/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.37  fof(c_0_7, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_8, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2)))))))), inference(assume_negation,[status(cth)],[t41_pre_topc])).
% 0.20/0.37  fof(c_0_10, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.37  cnf(c_0_11, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_12, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.37  fof(c_0_13, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.37  fof(c_0_14, negated_conjecture, ![X22]:(l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(esk4_0!=k1_struct_0(esk3_0)&(~m1_subset_1(X22,u1_struct_0(esk3_0))|~r2_hidden(X22,esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.20/0.37  cnf(c_0_15, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_17, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0]), ['final']).
% 0.20/0.37  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_21, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.20/0.37  cnf(c_0_24, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_25, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_19, c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_29, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (esk4_0!=k1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_xboole_0,X1)|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (X1!=esk4_0|~v1_xboole_0(k1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.37  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.37  cnf(c_0_34, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.37  fof(c_0_35, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.37  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_xboole_0,X1)|~v1_xboole_0(u1_struct_0(esk3_0))|~v1_xboole_0(k1_zfmisc_1(X2))|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~v1_xboole_0(u1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(k1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_27]), c_0_25]), ['final']).
% 0.20/0.37  cnf(c_0_40, plain, (r1_tarski(X1,X2)|r2_hidden(X3,X1)|~v1_xboole_0(esk2_2(X1,X2))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_12, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,X4)|~r2_hidden(X1,X3)|~v1_xboole_0(k1_zfmisc_1(X2))|~v1_xboole_0(X4)), inference(spm,[status(thm)],[c_0_18, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_42, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~v1_xboole_0(esk1_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(X3,X2)|~v1_xboole_0(esk2_2(X1,X2))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_33, c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (k1_struct_0(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 51
% 0.20/0.37  # Proof object clause steps            : 37
% 0.20/0.37  # Proof object formula steps           : 14
% 0.20/0.37  # Proof object conjectures             : 18
% 0.20/0.37  # Proof object clause conjectures      : 15
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 14
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 18
% 0.20/0.37  # Proof object simplifying inferences  : 7
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 15
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 15
% 0.20/0.37  # Processed clauses                    : 75
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 33
% 0.20/0.37  # ...remaining for further processing  : 40
% 0.20/0.37  # Other redundant clauses eliminated   : 2
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 8
% 0.20/0.37  # Generated clauses                    : 77
% 0.20/0.37  # ...of the previous two non-trivial   : 76
% 0.20/0.37  # Contextual simplify-reflections      : 2
% 0.20/0.37  # Paramodulations                      : 75
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 2
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 30
% 0.20/0.37  #    Positive orientable unit clauses  : 6
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 22
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 8
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 264
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 128
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 33
% 0.20/0.37  # Unit Clause-clause subsumption calls : 18
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 5
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1591
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.029 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
