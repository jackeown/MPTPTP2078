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
% DateTime   : Thu Dec  3 11:22:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 138 expanded)
%              Number of clauses        :   21 (  41 expanded)
%              Number of leaves         :    4 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 (1000 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2,X3] :
          ( ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) )
         => ( r1_waybel_0(X1,X3,X2)
           => ! [X4] :
                ( m2_yellow_6(X4,X1,X3)
               => r1_waybel_0(X1,X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow19)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(t27_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m2_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( r2_waybel_0(X1,X3,X4)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

fof(t9_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2,X3] :
            ( ( ~ v2_struct_0(X3)
              & v4_orders_2(X3)
              & v7_waybel_0(X3)
              & l1_waybel_0(X3,X1) )
           => ( r1_waybel_0(X1,X3,X2)
             => ! [X4] :
                  ( m2_yellow_6(X4,X1,X3)
                 => r1_waybel_0(X1,X4,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_yellow19])).

fof(c_0_5,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_struct_0(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( v4_orders_2(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( v7_waybel_0(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( l1_waybel_0(X10,X8)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & l1_waybel_0(esk3_0,esk1_0)
    & r1_waybel_0(esk1_0,esk3_0,esk2_0)
    & m2_yellow_6(esk4_0,esk1_0,esk3_0)
    & ~ r1_waybel_0(esk1_0,esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14] :
      ( v2_struct_0(X11)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X12)
      | ~ v4_orders_2(X12)
      | ~ v7_waybel_0(X12)
      | ~ l1_waybel_0(X12,X11)
      | ~ m2_yellow_6(X13,X11,X12)
      | ~ r2_waybel_0(X11,X13,X14)
      | r2_waybel_0(X11,X12,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_waybel_0(X5,X6,X7)
        | ~ r2_waybel_0(X5,X6,k6_subset_1(u1_struct_0(X5),X7))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) )
      & ( r2_waybel_0(X5,X6,k6_subset_1(u1_struct_0(X5),X7))
        | r1_waybel_0(X5,X6,X7)
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

cnf(c_0_9,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m2_yellow_6(esk4_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk3_0,X1)
    | ~ r2_waybel_0(esk1_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk4_0,k6_subset_1(u1_struct_0(esk1_0),X1))
    | r1_waybel_0(esk1_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])]),c_0_21]),c_0_16])).

cnf(c_0_24,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk3_0,k6_subset_1(u1_struct_0(esk1_0),X1))
    | r1_waybel_0(esk1_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,X1)
    | ~ r1_waybel_0(esk1_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t21_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2, X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m2_yellow_6(X4,X1,X3)=>r1_waybel_0(X1,X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow19)).
% 0.19/0.37  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.19/0.37  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.19/0.37  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2, X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m2_yellow_6(X4,X1,X3)=>r1_waybel_0(X1,X4,X2)))))), inference(assume_negation,[status(cth)],[t21_yellow19])).
% 0.19/0.37  fof(c_0_5, plain, ![X8, X9, X10]:((((~v2_struct_0(X10)|~m2_yellow_6(X10,X8,X9)|(v2_struct_0(X8)|~l1_struct_0(X8)|v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X8)))&(v4_orders_2(X10)|~m2_yellow_6(X10,X8,X9)|(v2_struct_0(X8)|~l1_struct_0(X8)|v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X8))))&(v7_waybel_0(X10)|~m2_yellow_6(X10,X8,X9)|(v2_struct_0(X8)|~l1_struct_0(X8)|v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X8))))&(l1_waybel_0(X10,X8)|~m2_yellow_6(X10,X8,X9)|(v2_struct_0(X8)|~l1_struct_0(X8)|v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_struct_0(esk1_0))&((((~v2_struct_0(esk3_0)&v4_orders_2(esk3_0))&v7_waybel_0(esk3_0))&l1_waybel_0(esk3_0,esk1_0))&(r1_waybel_0(esk1_0,esk3_0,esk2_0)&(m2_yellow_6(esk4_0,esk1_0,esk3_0)&~r1_waybel_0(esk1_0,esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X11, X12, X13, X14]:(v2_struct_0(X11)|~l1_struct_0(X11)|(v2_struct_0(X12)|~v4_orders_2(X12)|~v7_waybel_0(X12)|~l1_waybel_0(X12,X11)|(~m2_yellow_6(X13,X11,X12)|(~r2_waybel_0(X11,X13,X14)|r2_waybel_0(X11,X12,X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X5, X6, X7]:((~r1_waybel_0(X5,X6,X7)|~r2_waybel_0(X5,X6,k6_subset_1(u1_struct_0(X5),X7))|(v2_struct_0(X6)|~l1_waybel_0(X6,X5))|(v2_struct_0(X5)|~l1_struct_0(X5)))&(r2_waybel_0(X5,X6,k6_subset_1(u1_struct_0(X5),X7))|r1_waybel_0(X5,X6,X7)|(v2_struct_0(X6)|~l1_waybel_0(X6,X5))|(v2_struct_0(X5)|~l1_struct_0(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.19/0.37  cnf(c_0_9, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (m2_yellow_6(esk4_0,esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (v7_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (l1_waybel_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_17, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_19, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (l1_waybel_0(esk4_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_waybel_0(esk1_0,esk3_0,X1)|~r2_waybel_0(esk1_0,esk4_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_waybel_0(esk1_0,esk4_0,k6_subset_1(u1_struct_0(esk1_0),X1))|r1_waybel_0(esk1_0,esk4_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14])]), c_0_21]), c_0_16])).
% 0.19/0.37  cnf(c_0_24, plain, (v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_waybel_0(esk1_0,esk3_0,k6_subset_1(u1_struct_0(esk1_0),X1))|r1_waybel_0(esk1_0,esk4_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (~r1_waybel_0(esk1_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r1_waybel_0(esk1_0,esk4_0,X1)|~r1_waybel_0(esk1_0,esk3_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r1_waybel_0(esk1_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 30
% 0.19/0.37  # Proof object clause steps            : 21
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 32
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 41
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 41
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 12
% 0.19/0.37  # ...of the previous two non-trivial   : 9
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 12
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
% 0.19/0.37  # Current number of processed clauses  : 25
% 0.19/0.37  #    Positive orientable unit clauses  : 9
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 12
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 16
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 30
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 11
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1894
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
