%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:46 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 201 expanded)
%              Number of clauses        :   30 (  63 expanded)
%              Number of leaves         :    5 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  223 (1664 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m2_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r3_waybel_9(X1,X3,X4)
                   => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(d9_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,X2,X3)
              <=> ! [X4] :
                    ( m1_connsp_2(X4,X1,X3)
                   => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m2_yellow_6(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_waybel_9(X1,X3,X4)
                     => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_waybel_9])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r3_waybel_9(X13,X14,X15)
        | ~ m1_connsp_2(X16,X13,X15)
        | r2_waybel_0(X13,X14,X16)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_connsp_2(esk1_3(X13,X14,X15),X13,X15)
        | r3_waybel_9(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_waybel_0(X13,X14,esk1_3(X13,X14,X15))
        | r3_waybel_9(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & l1_waybel_0(esk3_0,esk2_0)
    & m2_yellow_6(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & r3_waybel_9(esk2_0,esk4_0,esk5_0)
    & ~ r3_waybel_9(esk2_0,esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( m1_connsp_2(esk1_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v2_struct_0(X8)
        | ~ m2_yellow_6(X8,X6,X7)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6) )
      & ( v4_orders_2(X8)
        | ~ m2_yellow_6(X8,X6,X7)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6) )
      & ( v7_waybel_0(X8)
        | ~ m2_yellow_6(X8,X6,X7)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6) )
      & ( l1_waybel_0(X8,X6)
        | ~ m2_yellow_6(X8,X6,X7)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_15,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_connsp_2(X4,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk2_0,X1,esk5_0),esk2_0,esk5_0)
    | r3_waybel_9(esk2_0,X1,esk5_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m2_yellow_6(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_waybel_0(esk2_0,X1,X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X2,esk2_0,esk5_0)
    | ~ r3_waybel_9(esk2_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk2_0,esk3_0,esk5_0),esk2_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_27,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17]),c_0_23]),c_0_24])]),c_0_19]),c_0_12])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | v2_struct_0(X10)
      | ~ v4_orders_2(X10)
      | ~ v7_waybel_0(X10)
      | ~ l1_waybel_0(X10,X9)
      | ~ m2_yellow_6(X11,X9,X10)
      | ~ r2_waybel_0(X9,X11,X12)
      | r2_waybel_0(X9,X10,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_waybel_0(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk2_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r3_waybel_9(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_17]),c_0_23]),c_0_24]),c_0_28])]),c_0_19]),c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk2_0,esk4_0,esk1_3(esk2_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_waybel_0(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk4_0,esk2_0,X1)
    | ~ l1_waybel_0(X1,esk2_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])]),c_0_12])).

cnf(c_0_38,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( r2_waybel_0(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_17]),c_0_23]),c_0_24])]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_9]),c_0_10]),c_0_17]),c_0_11])]),c_0_18]),c_0_19]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:21:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.028 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t31_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.12/0.36  fof(d9_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>![X4]:(m1_connsp_2(X4,X1,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_waybel_9)).
% 0.12/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.37  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.12/0.37  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t31_waybel_9])).
% 0.12/0.37  fof(c_0_6, plain, ![X13, X14, X15, X16]:((~r3_waybel_9(X13,X14,X15)|(~m1_connsp_2(X16,X13,X15)|r2_waybel_0(X13,X14,X16))|~m1_subset_1(X15,u1_struct_0(X13))|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((m1_connsp_2(esk1_3(X13,X14,X15),X13,X15)|r3_waybel_9(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_waybel_0(X13,X14,esk1_3(X13,X14,X15))|r3_waybel_9(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((((~v2_struct_0(esk3_0)&v4_orders_2(esk3_0))&v7_waybel_0(esk3_0))&l1_waybel_0(esk3_0,esk2_0))&(m2_yellow_6(esk4_0,esk2_0,esk3_0)&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(r3_waybel_9(esk2_0,esk4_0,esk5_0)&~r3_waybel_9(esk2_0,esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.12/0.37  cnf(c_0_8, plain, (m1_connsp_2(esk1_3(X1,X2,X3),X1,X3)|r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  fof(c_0_13, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.37  fof(c_0_14, plain, ![X6, X7, X8]:((((~v2_struct_0(X8)|~m2_yellow_6(X8,X6,X7)|(v2_struct_0(X6)|~l1_struct_0(X6)|v2_struct_0(X7)|~v4_orders_2(X7)|~v7_waybel_0(X7)|~l1_waybel_0(X7,X6)))&(v4_orders_2(X8)|~m2_yellow_6(X8,X6,X7)|(v2_struct_0(X6)|~l1_struct_0(X6)|v2_struct_0(X7)|~v4_orders_2(X7)|~v7_waybel_0(X7)|~l1_waybel_0(X7,X6))))&(v7_waybel_0(X8)|~m2_yellow_6(X8,X6,X7)|(v2_struct_0(X6)|~l1_struct_0(X6)|v2_struct_0(X7)|~v4_orders_2(X7)|~v7_waybel_0(X7)|~l1_waybel_0(X7,X6))))&(l1_waybel_0(X8,X6)|~m2_yellow_6(X8,X6,X7)|(v2_struct_0(X6)|~l1_struct_0(X6)|v2_struct_0(X7)|~v4_orders_2(X7)|~v7_waybel_0(X7)|~l1_waybel_0(X7,X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_connsp_2(X4,X1,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_connsp_2(esk1_3(esk2_0,X1,esk5_0),esk2_0,esk5_0)|r3_waybel_9(esk2_0,X1,esk5_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])]), c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (~r3_waybel_9(esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_20, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_21, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m2_yellow_6(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v7_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r2_waybel_0(esk2_0,X1,X2)|v2_struct_0(X1)|~m1_connsp_2(X2,esk2_0,esk5_0)|~r3_waybel_9(esk2_0,X1,esk5_0)|~l1_waybel_0(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_9]), c_0_10]), c_0_11])]), c_0_12])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_connsp_2(esk1_3(esk2_0,esk3_0,esk5_0),esk2_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.37  cnf(c_0_27, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_11])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17]), c_0_23]), c_0_24])]), c_0_19]), c_0_12])).
% 0.12/0.37  fof(c_0_30, plain, ![X9, X10, X11, X12]:(v2_struct_0(X9)|~l1_struct_0(X9)|(v2_struct_0(X10)|~v4_orders_2(X10)|~v7_waybel_0(X10)|~l1_waybel_0(X10,X9)|(~m2_yellow_6(X11,X9,X10)|(~r2_waybel_0(X9,X11,X12)|r2_waybel_0(X9,X10,X12))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r2_waybel_0(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))|v2_struct_0(X1)|~r3_waybel_9(esk2_0,X1,esk5_0)|~l1_waybel_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (r3_waybel_9(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (l1_waybel_0(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_17]), c_0_23]), c_0_24]), c_0_28])]), c_0_19]), c_0_12])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28])])).
% 0.12/0.37  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r2_waybel_0(esk2_0,esk4_0,esk1_3(esk2_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (r2_waybel_0(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))|v2_struct_0(X1)|~m2_yellow_6(esk4_0,esk2_0,X1)|~l1_waybel_0(X1,esk2_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])]), c_0_12])).
% 0.12/0.37  cnf(c_0_38, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r2_waybel_0(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_17]), c_0_23]), c_0_24])]), c_0_19])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_9]), c_0_10]), c_0_17]), c_0_11])]), c_0_18]), c_0_19]), c_0_12]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 30
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 11
% 0.12/0.37  # Proof object simplifying inferences  : 44
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 20
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 20
% 0.12/0.37  # Processed clauses                    : 53
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 53
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 15
% 0.12/0.37  # ...of the previous two non-trivial   : 14
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 15
% 0.12/0.37  # Factorizations                       : 0
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
% 0.12/0.37  # Current number of processed clauses  : 32
% 0.12/0.37  #    Positive orientable unit clauses  : 15
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 13
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 21
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 89
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 14
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2385
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
