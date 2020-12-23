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
% DateTime   : Thu Dec  3 11:21:20 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 133 expanded)
%              Number of clauses        :   21 (  39 expanded)
%              Number of leaves         :    6 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 (1025 expanded)
%              Number of equality atoms :    8 (  89 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => k11_yellow_6(X1,X2) = k4_yellow_6(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

fof(t42_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(cc4_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v1_yellow_6(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v3_yellow_6(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(d20_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v3_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X3 = k11_yellow_6(X1,X2)
              <=> r2_hidden(X3,k10_yellow_6(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v1_yellow_6(X2,X1)
              & l1_waybel_0(X2,X1) )
           => k11_yellow_6(X1,X2) = k4_yellow_6(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_6])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ v4_orders_2(X13)
      | ~ v7_waybel_0(X13)
      | ~ v1_yellow_6(X13,X12)
      | ~ l1_waybel_0(X13,X12)
      | r2_hidden(k4_yellow_6(X12,X13),k10_yellow_6(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & v8_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & v1_yellow_6(esk2_0,esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & k11_yellow_6(esk1_0,esk2_0) != k4_yellow_6(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ v1_yellow_6(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v4_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ v1_yellow_6(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v7_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ v1_yellow_6(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v3_yellow_6(X6,X5)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ v1_yellow_6(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).

fof(c_0_10,plain,(
    ! [X7,X8,X9] :
      ( ( X9 != k11_yellow_6(X7,X8)
        | r2_hidden(X9,k10_yellow_6(X7,X8))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ v3_yellow_6(X8,X7)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v8_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(X9,k10_yellow_6(X7,X8))
        | X9 = k11_yellow_6(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ v3_yellow_6(X8,X7)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v8_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_yellow_6(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( v3_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v1_yellow_6(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ l1_waybel_0(X11,X10)
      | m1_subset_1(k4_yellow_6(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_22,plain,
    ( X1 = k11_yellow_6(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ v3_yellow_6(X3,X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ v8_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk1_0,esk2_0),k10_yellow_6(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( v3_yellow_6(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_19]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k11_yellow_6(esk1_0,esk2_0) != k4_yellow_6(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_6(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_26]),c_0_18]),c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_19])).

fof(c_0_30,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_31,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:54:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t45_yellow_6, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 0.18/0.37  fof(t42_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.18/0.37  fof(cc4_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(l1_waybel_0(X2,X1)=>((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))=>(((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 0.18/0.37  fof(d20_yellow_6, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k11_yellow_6(X1,X2)<=>r2_hidden(X3,k10_yellow_6(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 0.18/0.37  fof(dt_k4_yellow_6, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_struct_0(X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 0.18/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2)))), inference(assume_negation,[status(cth)],[t45_yellow_6])).
% 0.18/0.37  fof(c_0_7, plain, ![X12, X13]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~v1_yellow_6(X13,X12)|~l1_waybel_0(X13,X12)|r2_hidden(k4_yellow_6(X12,X13),k10_yellow_6(X12,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).
% 0.18/0.37  fof(c_0_8, negated_conjecture, ((((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&v8_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v2_struct_0(esk2_0)&v4_orders_2(esk2_0))&v7_waybel_0(esk2_0))&v1_yellow_6(esk2_0,esk1_0))&l1_waybel_0(esk2_0,esk1_0))&k11_yellow_6(esk1_0,esk2_0)!=k4_yellow_6(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.18/0.37  fof(c_0_9, plain, ![X5, X6]:((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v4_orders_2(X6)|~v7_waybel_0(X6)|~v1_yellow_6(X6,X5))|~l1_waybel_0(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(v4_orders_2(X6)|(v2_struct_0(X6)|~v4_orders_2(X6)|~v7_waybel_0(X6)|~v1_yellow_6(X6,X5))|~l1_waybel_0(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v7_waybel_0(X6)|(v2_struct_0(X6)|~v4_orders_2(X6)|~v7_waybel_0(X6)|~v1_yellow_6(X6,X5))|~l1_waybel_0(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v3_yellow_6(X6,X5)|(v2_struct_0(X6)|~v4_orders_2(X6)|~v7_waybel_0(X6)|~v1_yellow_6(X6,X5))|~l1_waybel_0(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).
% 0.18/0.37  fof(c_0_10, plain, ![X7, X8, X9]:((X9!=k11_yellow_6(X7,X8)|r2_hidden(X9,k10_yellow_6(X7,X8))|~m1_subset_1(X9,u1_struct_0(X7))|(v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~v3_yellow_6(X8,X7)|~l1_waybel_0(X8,X7))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~v8_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(X9,k10_yellow_6(X7,X8))|X9=k11_yellow_6(X7,X8)|~m1_subset_1(X9,u1_struct_0(X7))|(v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~v3_yellow_6(X8,X7)|~l1_waybel_0(X8,X7))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~v8_pre_topc(X7)|~l1_pre_topc(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).
% 0.18/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  cnf(c_0_12, negated_conjecture, (v1_yellow_6(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_13, negated_conjecture, (v7_waybel_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_14, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_15, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_20, plain, (v3_yellow_6(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v1_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_21, plain, ![X10, X11]:(v2_struct_0(X10)|~l1_struct_0(X10)|~l1_waybel_0(X11,X10)|m1_subset_1(k4_yellow_6(X10,X11),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).
% 0.18/0.37  cnf(c_0_22, plain, (X1=k11_yellow_6(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~v3_yellow_6(X3,X2)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~v8_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_yellow_6(esk1_0,esk2_0),k10_yellow_6(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (v8_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (v3_yellow_6(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_19]), c_0_18])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (k11_yellow_6(esk1_0,esk2_0)!=k4_yellow_6(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (~m1_subset_1(k4_yellow_6(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_26]), c_0_18]), c_0_19])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(k4_yellow_6(esk1_0,esk2_0),u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_19])).
% 0.18/0.37  fof(c_0_30, plain, ![X4]:(~l1_pre_topc(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (~l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.37  cnf(c_0_32, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17])]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 34
% 0.18/0.37  # Proof object clause steps            : 21
% 0.18/0.37  # Proof object formula steps           : 13
% 0.18/0.37  # Proof object conjectures             : 19
% 0.18/0.37  # Proof object clause conjectures      : 16
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 15
% 0.18/0.37  # Proof object initial formulas used   : 6
% 0.18/0.37  # Proof object generating inferences   : 6
% 0.18/0.37  # Proof object simplifying inferences  : 30
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 6
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 19
% 0.18/0.37  # Removed in clause preprocessing      : 3
% 0.18/0.37  # Initial clauses in saturation        : 16
% 0.18/0.37  # Processed clauses                    : 37
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 0
% 0.18/0.37  # ...remaining for further processing  : 37
% 0.18/0.37  # Other redundant clauses eliminated   : 1
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 0
% 0.18/0.37  # Generated clauses                    : 7
% 0.18/0.37  # ...of the previous two non-trivial   : 6
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 6
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 1
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
% 0.18/0.37  # Current number of processed clauses  : 20
% 0.18/0.37  #    Positive orientable unit clauses  : 9
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 5
% 0.18/0.37  #    Non-unit-clauses                  : 6
% 0.18/0.37  # Current number of unprocessed clauses: 1
% 0.18/0.37  # ...number of literals in the above   : 11
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 16
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 114
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.37  # Unit Clause-clause subsumption calls : 2
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 0
% 0.18/0.37  # BW rewrite match successes           : 0
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 1997
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.031 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.033 s
% 0.18/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
