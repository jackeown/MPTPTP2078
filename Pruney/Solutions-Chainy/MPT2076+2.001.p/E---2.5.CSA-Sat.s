%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:05 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 654 expanded)
%              Number of clauses        :   29 ( 204 expanded)
%              Number of leaves         :    2 ( 162 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 (8588 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).

fof(l38_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) )
       => v1_compts_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v4_orders_2(X2)
                & v7_waybel_0(X2)
                & l1_waybel_0(X2,X1) )
             => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ~ r3_waybel_9(X1,X2,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_yellow19])).

fof(c_0_3,plain,(
    ! [X4,X6] :
      ( ( ~ v2_struct_0(esk1_1(X4))
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v4_orders_2(esk1_1(X4))
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v7_waybel_0(esk1_1(X4))
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( l1_waybel_0(esk1_1(X4),X4)
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk1_1(X4),k6_yellow_6(X4))
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ r3_waybel_9(X4,esk1_1(X4),X6)
        | v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X9,X10] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ( ~ v2_struct_0(esk3_0)
        | ~ v1_compts_1(esk2_0) )
      & ( v4_orders_2(esk3_0)
        | ~ v1_compts_1(esk2_0) )
      & ( v7_waybel_0(esk3_0)
        | ~ v1_compts_1(esk2_0) )
      & ( l1_waybel_0(esk3_0,esk2_0)
        | ~ v1_compts_1(esk2_0) )
      & ( r2_hidden(esk3_0,k6_yellow_6(esk2_0))
        | ~ v1_compts_1(esk2_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk2_0))
        | ~ r3_waybel_9(esk2_0,esk3_0,X9)
        | ~ v1_compts_1(esk2_0) )
      & ( m1_subset_1(esk4_1(X10),u1_struct_0(esk2_0))
        | ~ r2_hidden(X10,k6_yellow_6(esk2_0))
        | v2_struct_0(X10)
        | ~ v4_orders_2(X10)
        | ~ v7_waybel_0(X10)
        | ~ l1_waybel_0(X10,esk2_0)
        | v1_compts_1(esk2_0) )
      & ( r3_waybel_9(esk2_0,X10,esk4_1(X10))
        | ~ r2_hidden(X10,k6_yellow_6(esk2_0))
        | v2_struct_0(X10)
        | ~ v4_orders_2(X10)
        | ~ v7_waybel_0(X10)
        | ~ l1_waybel_0(X10,esk2_0)
        | v1_compts_1(esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk1_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r3_waybel_9(esk2_0,X1,esk4_1(X1))
    | v2_struct_0(X1)
    | v1_compts_1(esk2_0)
    | ~ r2_hidden(X1,k6_yellow_6(esk2_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | v1_compts_1(esk2_0)
    | ~ r2_hidden(X1,k6_yellow_6(esk2_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v1_compts_1(esk2_0)
    | v2_struct_0(esk1_1(esk2_0))
    | ~ r2_hidden(esk1_1(esk2_0),k6_yellow_6(esk2_0))
    | ~ l1_waybel_0(esk1_1(esk2_0),esk2_0)
    | ~ v7_waybel_0(esk1_1(esk2_0))
    | ~ v4_orders_2(esk1_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_1(X1),k6_yellow_6(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( v1_compts_1(esk2_0)
    | v2_struct_0(esk1_1(esk2_0))
    | ~ l1_waybel_0(esk1_1(esk2_0),esk2_0)
    | ~ v7_waybel_0(esk1_1(esk2_0))
    | ~ v4_orders_2(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_14,plain,
    ( l1_waybel_0(esk1_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( v1_compts_1(esk2_0)
    | v2_struct_0(esk1_1(esk2_0))
    | ~ v7_waybel_0(esk1_1(esk2_0))
    | ~ v4_orders_2(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_16,plain,
    ( v7_waybel_0(esk1_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( v1_compts_1(esk2_0)
    | v2_struct_0(esk1_1(esk2_0))
    | ~ v4_orders_2(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_18,plain,
    ( v4_orders_2(esk1_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_19,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( v1_compts_1(esk2_0)
    | v2_struct_0(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r3_waybel_9(esk2_0,esk3_0,X1)
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( v1_compts_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_7]),c_0_8])]),c_0_9]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,k6_yellow_6(esk2_0))
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0)
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk3_0)
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( v7_waybel_0(esk3_0)
    | ~ v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_22])]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,k6_yellow_6(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22])]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22])]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  
% 0.12/0.36  # No proof found!
% 0.12/0.36  # SZS status CounterSatisfiable
% 0.12/0.36  # SZS output start Saturation
% 0.12/0.36  fof(t36_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_yellow19)).
% 0.12/0.36  fof(l38_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3))))))=>v1_compts_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_yellow19)).
% 0.12/0.36  fof(c_0_2, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3))))))))), inference(assume_negation,[status(cth)],[t36_yellow19])).
% 0.12/0.36  fof(c_0_3, plain, ![X4, X6]:(((((~v2_struct_0(esk1_1(X4))|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)))&(v4_orders_2(esk1_1(X4))|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(v7_waybel_0(esk1_1(X4))|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(l1_waybel_0(esk1_1(X4),X4)|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&((r2_hidden(esk1_1(X4),k6_yellow_6(X4))|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)))&(~m1_subset_1(X6,u1_struct_0(X4))|~r3_waybel_9(X4,esk1_1(X4),X6)|v1_compts_1(X4)|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).
% 0.12/0.36  fof(c_0_4, negated_conjecture, ![X9, X10]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((((((~v2_struct_0(esk3_0)|~v1_compts_1(esk2_0))&(v4_orders_2(esk3_0)|~v1_compts_1(esk2_0)))&(v7_waybel_0(esk3_0)|~v1_compts_1(esk2_0)))&(l1_waybel_0(esk3_0,esk2_0)|~v1_compts_1(esk2_0)))&((r2_hidden(esk3_0,k6_yellow_6(esk2_0))|~v1_compts_1(esk2_0))&(~m1_subset_1(X9,u1_struct_0(esk2_0))|~r3_waybel_9(esk2_0,esk3_0,X9)|~v1_compts_1(esk2_0))))&((m1_subset_1(esk4_1(X10),u1_struct_0(esk2_0))|~r2_hidden(X10,k6_yellow_6(esk2_0))|(v2_struct_0(X10)|~v4_orders_2(X10)|~v7_waybel_0(X10)|~l1_waybel_0(X10,esk2_0))|v1_compts_1(esk2_0))&(r3_waybel_9(esk2_0,X10,esk4_1(X10))|~r2_hidden(X10,k6_yellow_6(esk2_0))|(v2_struct_0(X10)|~v4_orders_2(X10)|~v7_waybel_0(X10)|~l1_waybel_0(X10,esk2_0))|v1_compts_1(esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).
% 0.12/0.36  cnf(c_0_5, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk1_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_6, negated_conjecture, (r3_waybel_9(esk2_0,X1,esk4_1(X1))|v2_struct_0(X1)|v1_compts_1(esk2_0)|~r2_hidden(X1,k6_yellow_6(esk2_0))|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))|v2_struct_0(X1)|v1_compts_1(esk2_0)|~r2_hidden(X1,k6_yellow_6(esk2_0))|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (v1_compts_1(esk2_0)|v2_struct_0(esk1_1(esk2_0))|~r2_hidden(esk1_1(esk2_0),k6_yellow_6(esk2_0))|~l1_waybel_0(esk1_1(esk2_0),esk2_0)|~v7_waybel_0(esk1_1(esk2_0))|~v4_orders_2(esk1_1(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), c_0_8])]), c_0_9]), c_0_10])).
% 0.12/0.36  cnf(c_0_12, plain, (r2_hidden(esk1_1(X1),k6_yellow_6(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (v1_compts_1(esk2_0)|v2_struct_0(esk1_1(esk2_0))|~l1_waybel_0(esk1_1(esk2_0),esk2_0)|~v7_waybel_0(esk1_1(esk2_0))|~v4_orders_2(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_7]), c_0_8])]), c_0_9])).
% 0.12/0.36  cnf(c_0_14, plain, (l1_waybel_0(esk1_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (v1_compts_1(esk2_0)|v2_struct_0(esk1_1(esk2_0))|~v7_waybel_0(esk1_1(esk2_0))|~v4_orders_2(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_7]), c_0_8])]), c_0_9])).
% 0.12/0.36  cnf(c_0_16, plain, (v7_waybel_0(esk1_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (v1_compts_1(esk2_0)|v2_struct_0(esk1_1(esk2_0))|~v4_orders_2(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_7]), c_0_8])]), c_0_9])).
% 0.12/0.36  cnf(c_0_18, plain, (v4_orders_2(esk1_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_19, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk1_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (v1_compts_1(esk2_0)|v2_struct_0(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_7]), c_0_8])]), c_0_9])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r3_waybel_9(esk2_0,esk3_0,X1)|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (v1_compts_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_7]), c_0_8])]), c_0_9]), ['final']).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_0,k6_yellow_6(esk2_0))|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (v4_orders_2(esk3_0)|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (v7_waybel_0(esk3_0)|~v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (~r3_waybel_9(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])]), ['final']).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_22])]), ['final']).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,k6_yellow_6(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22])]), ['final']).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22])]), ['final']).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (v4_orders_2(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22])]), ['final']).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (v7_waybel_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22])]), ['final']).
% 0.12/0.36  # SZS output end Saturation
% 0.12/0.36  # Proof object total steps             : 34
% 0.12/0.36  # Proof object clause steps            : 29
% 0.12/0.36  # Proof object formula steps           : 5
% 0.12/0.36  # Proof object conjectures             : 26
% 0.12/0.36  # Proof object clause conjectures      : 23
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 17
% 0.12/0.36  # Proof object initial formulas used   : 2
% 0.12/0.36  # Proof object generating inferences   : 6
% 0.12/0.36  # Proof object simplifying inferences  : 37
% 0.12/0.36  # Parsed axioms                        : 2
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 17
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 17
% 0.12/0.36  # Processed clauses                    : 29
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 29
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 4
% 0.12/0.36  # Backward-rewritten                   : 9
% 0.12/0.36  # Generated clauses                    : 7
% 0.12/0.36  # ...of the previous two non-trivial   : 12
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 7
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 16
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 7
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 13
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 20
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 5
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1625
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
