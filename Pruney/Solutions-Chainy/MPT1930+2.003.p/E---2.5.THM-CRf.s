%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  65 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  102 ( 370 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
             => r2_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(t10_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ~ r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t26_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ~ ( r1_waybel_0(X1,X2,X3)
                & r1_waybel_0(X1,X2,X4)
                & r1_xboole_0(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( r1_waybel_0(X1,X2,X3)
               => r2_waybel_0(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_yellow_6])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r2_waybel_0(X9,X10,X11)
        | ~ r1_waybel_0(X9,X10,k6_subset_1(u1_struct_0(X9),X11))
        | v2_struct_0(X10)
        | ~ l1_waybel_0(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_struct_0(X9) )
      & ( r1_waybel_0(X9,X10,k6_subset_1(u1_struct_0(X9),X11))
        | r2_waybel_0(X9,X10,X11)
        | v2_struct_0(X10)
        | ~ l1_waybel_0(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_struct_0(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8] : k6_subset_1(X7,X8) = k4_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | v2_struct_0(X13)
      | ~ v4_orders_2(X13)
      | ~ v7_waybel_0(X13)
      | ~ l1_waybel_0(X13,X12)
      | ~ r1_waybel_0(X12,X13,X14)
      | ~ r1_waybel_0(X12,X13,X15)
      | ~ r1_xboole_0(X14,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & r1_waybel_0(esk1_0,esk2_0,esk3_0)
    & ~ r2_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_10,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,k4_xboole_0(u1_struct_0(esk1_0),X1))
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

fof(c_0_23,plain,(
    ! [X5,X6] : r1_xboole_0(k4_xboole_0(X5,X6),X6) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_24,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,X1)
    | ~ r1_xboole_0(k4_xboole_0(u1_struct_0(esk1_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S083N
% 0.19/0.37  # and selection function SelectCQArNT.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t28_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_yellow_6)).
% 0.19/0.37  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.19/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.37  fof(t26_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:~(((r1_waybel_0(X1,X2,X3)&r1_waybel_0(X1,X2,X4))&r1_xboole_0(X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_6)).
% 0.19/0.37  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X3))))), inference(assume_negation,[status(cth)],[t28_yellow_6])).
% 0.19/0.37  fof(c_0_6, plain, ![X9, X10, X11]:((~r2_waybel_0(X9,X10,X11)|~r1_waybel_0(X9,X10,k6_subset_1(u1_struct_0(X9),X11))|(v2_struct_0(X10)|~l1_waybel_0(X10,X9))|(v2_struct_0(X9)|~l1_struct_0(X9)))&(r1_waybel_0(X9,X10,k6_subset_1(u1_struct_0(X9),X11))|r2_waybel_0(X9,X10,X11)|(v2_struct_0(X10)|~l1_waybel_0(X10,X9))|(v2_struct_0(X9)|~l1_struct_0(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X7, X8]:k6_subset_1(X7,X8)=k4_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X12, X13, X14, X15]:(v2_struct_0(X12)|~l1_struct_0(X12)|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12)|(~r1_waybel_0(X12,X13,X14)|~r1_waybel_0(X12,X13,X15)|~r1_xboole_0(X14,X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_struct_0(esk1_0))&((((~v2_struct_0(esk2_0)&v4_orders_2(esk2_0))&v7_waybel_0(esk2_0))&l1_waybel_0(esk2_0,esk1_0))&(r1_waybel_0(esk1_0,esk2_0,esk3_0)&~r2_waybel_0(esk1_0,esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.19/0.37  cnf(c_0_10, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~r1_waybel_0(X1,X2,X3)|~r1_waybel_0(X1,X2,X4)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (r1_waybel_0(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v7_waybel_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_20, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (~r1_waybel_0(esk1_0,esk2_0,X1)|~r1_xboole_0(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r1_waybel_0(esk1_0,esk2_0,k4_xboole_0(u1_struct_0(esk1_0),X1))|r2_waybel_0(esk1_0,esk2_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.19/0.37  fof(c_0_23, plain, ![X5, X6]:r1_xboole_0(k4_xboole_0(X5,X6),X6), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (r2_waybel_0(esk1_0,esk2_0,X1)|~r1_xboole_0(k4_xboole_0(u1_struct_0(esk1_0),X1),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.37  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (~r2_waybel_0(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 28
% 0.19/0.37  # Proof object clause steps            : 17
% 0.19/0.37  # Proof object formula steps           : 11
% 0.19/0.37  # Proof object conjectures             : 15
% 0.19/0.37  # Proof object clause conjectures      : 12
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 5
% 0.19/0.37  # Proof object generating inferences   : 4
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 5
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 13
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 12
% 0.19/0.37  # Processed clauses                    : 29
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 29
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 9
% 0.19/0.37  # ...of the previous two non-trivial   : 7
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 9
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 17
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 7
% 0.19/0.37  # Current number of unprocessed clauses: 2
% 0.19/0.37  # ...number of literals in the above   : 5
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1235
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
