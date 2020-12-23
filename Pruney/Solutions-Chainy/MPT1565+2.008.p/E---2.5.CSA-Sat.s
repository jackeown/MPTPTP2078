%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:31 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 105 expanded)
%              Number of clauses        :   30 (  38 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :  178 ( 546 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_yellow_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( r2_yellow_0(X1,k1_xboole_0)
          & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t43_yellow_0])).

fof(c_0_10,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v5_orders_2(esk3_0)
    & v2_yellow_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ( ~ r2_yellow_0(esk3_0,k1_xboole_0)
      | ~ r1_yellow_0(esk3_0,u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk1_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk2_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_14,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | ~ r1_tarski(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_22,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_25,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_28,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X2)
    | ~ r1_lattice3(esk3_0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X2)
    | ~ r2_lattice3(esk3_0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk2_3(esk3_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk1_3(esk3_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r2_hidden(esk2_3(esk3_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,X2,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r2_hidden(esk1_3(esk3_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16]),
    [final]).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,k1_xboole_0)
    | ~ r1_yellow_0(esk3_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [final]).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( v2_yellow_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S073A
% 0.18/0.37  # and selection function SelectCQIArEqLast.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.027 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # No proof found!
% 0.18/0.37  # SZS status CounterSatisfiable
% 0.18/0.37  # SZS output start Saturation
% 0.18/0.37  fof(t43_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>(r2_yellow_0(X1,k1_xboole_0)&r1_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_yellow_0)).
% 0.18/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.18/0.37  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.18/0.37  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.18/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.18/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.18/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>(r2_yellow_0(X1,k1_xboole_0)&r1_yellow_0(X1,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t43_yellow_0])).
% 0.18/0.37  fof(c_0_10, plain, ![X13]:(~l1_orders_2(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk3_0)&v5_orders_2(esk3_0))&v2_yellow_0(esk3_0))&l1_orders_2(esk3_0))&(~r2_yellow_0(esk3_0,k1_xboole_0)|~r1_yellow_0(esk3_0,u1_struct_0(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.18/0.37  fof(c_0_12, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X16,X17)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk1_3(X14,X15,X16),X15)|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,X16,esk1_3(X14,X15,X16))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.18/0.37  fof(c_0_13, plain, ![X19, X20, X21, X22]:((~r2_lattice3(X19,X20,X21)|(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X20)|r1_orders_2(X19,X22,X21)))|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((r2_hidden(esk2_3(X19,X20,X21),X20)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&(~r1_orders_2(X19,esk2_3(X19,X20,X21),X21)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.18/0.37  fof(c_0_14, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.18/0.37  cnf(c_0_15, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.37  fof(c_0_17, plain, ![X10, X11]:(~r2_hidden(X10,X11)|~r1_tarski(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.37  fof(c_0_18, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.37  cnf(c_0_19, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.37  cnf(c_0_20, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_21, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_22, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.37  cnf(c_0_24, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_25, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.37  fof(c_0_27, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.18/0.37  fof(c_0_28, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.18/0.37  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk3_0,X1,X2)|~r1_lattice3(esk3_0,X3,X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (r1_orders_2(esk3_0,X1,X2)|~r2_lattice3(esk3_0,X3,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|m1_subset_1(esk2_3(esk3_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|m1_subset_1(esk1_3(esk3_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r2_hidden(esk2_3(esk3_0,X1,X2),X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,X2,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r2_hidden(esk1_3(esk3_0,X1,X2),X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_16]), ['final']).
% 0.18/0.37  cnf(c_0_42, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.18/0.37  cnf(c_0_43, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (~r2_yellow_0(esk3_0,k1_xboole_0)|~r1_yellow_0(esk3_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), ['final']).
% 0.18/0.37  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (v2_yellow_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.37  # SZS output end Saturation
% 0.18/0.37  # Proof object total steps             : 49
% 0.18/0.37  # Proof object clause steps            : 30
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 18
% 0.18/0.37  # Proof object clause conjectures      : 15
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 19
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 11
% 0.18/0.37  # Proof object simplifying inferences  : 1
% 0.18/0.37  # Parsed axioms                        : 9
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 19
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 19
% 0.18/0.37  # Processed clauses                    : 49
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 0
% 0.18/0.37  # ...remaining for further processing  : 49
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 0
% 0.18/0.37  # Generated clauses                    : 11
% 0.18/0.37  # ...of the previous two non-trivial   : 11
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 11
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 0
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 30
% 0.18/0.37  #    Positive orientable unit clauses  : 5
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 3
% 0.18/0.37  #    Non-unit-clauses                  : 22
% 0.18/0.37  # Current number of unprocessed clauses: 0
% 0.18/0.37  # ...number of literals in the above   : 0
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 19
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 232
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 66
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.37  # Unit Clause-clause subsumption calls : 2
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 0
% 0.18/0.37  # BW rewrite match successes           : 0
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 1894
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.030 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.033 s
% 0.18/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
