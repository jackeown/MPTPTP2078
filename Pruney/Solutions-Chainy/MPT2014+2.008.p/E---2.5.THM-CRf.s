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
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 232 expanded)
%              Number of clauses        :   31 (  81 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 (1068 expanded)
%              Number of equality atoms :   12 (  35 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(t12_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

fof(fraenkel_a_3_0_waybel_9,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2)
        & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
      <=> ? [X5] :
            ( m1_subset_1(X5,u1_struct_0(X3))
            & X1 = X5
            & r1_orders_2(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_waybel_9])).

fof(c_0_9,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v2_struct_0(X25)
      | ~ l1_waybel_0(X25,X24)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | u1_struct_0(k4_waybel_9(X24,X25,X26)) = a_3_0_waybel_9(X24,X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_waybel_9])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & l1_waybel_0(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X18,X19,X20,X21,X23] :
      ( ( m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( X18 = esk2_4(X18,X19,X20,X21)
        | ~ r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( r1_orders_2(X20,X21,esk2_4(X18,X19,X20,X21))
        | ~ r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | X18 != X23
        | ~ r1_orders_2(X20,X21,X23)
        | r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = esk2_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk3_0,esk4_0,X1)) = a_3_0_waybel_9(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( esk2_4(X1,esk3_0,esk4_0,X2) = X1
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0)),u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)) = a_3_0_waybel_9(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk3_0,esk4_0,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( esk2_4(X1,esk3_0,esk4_0,esk5_0) = X1
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

fof(c_0_30,plain,(
    ! [X16,X17] :
      ( ~ l1_struct_0(X16)
      | ~ l1_waybel_0(X17,X16)
      | l1_orders_2(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0) = esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_35,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_33])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_15])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.40  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.051 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.20/0.40  fof(t12_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_waybel_9)).
% 0.20/0.40  fof(fraenkel_a_3_0_waybel_9, axiom, ![X1, X2, X3, X4]:(((((~(v2_struct_0(X2))&l1_struct_0(X2))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X2))&m1_subset_1(X4,u1_struct_0(X3)))=>(r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))<=>?[X5]:((m1_subset_1(X5,u1_struct_0(X3))&X1=X5)&r1_orders_2(X3,X4,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.40  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.20/0.40  fof(c_0_9, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~l1_struct_0(X24)|(v2_struct_0(X25)|~l1_waybel_0(X25,X24)|(~m1_subset_1(X26,u1_struct_0(X25))|u1_struct_0(k4_waybel_9(X24,X25,X26))=a_3_0_waybel_9(X24,X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_waybel_9])])])])).
% 0.20/0.40  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&((~v2_struct_0(esk4_0)&l1_waybel_0(esk4_0,esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.40  fof(c_0_11, plain, ![X18, X19, X20, X21, X23]:((((m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X20))|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20))))&(X18=esk2_4(X18,X19,X20,X21)|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20)))))&(r1_orders_2(X20,X21,esk2_4(X18,X19,X20,X21))|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20)))))&(~m1_subset_1(X23,u1_struct_0(X20))|X18!=X23|~r1_orders_2(X20,X21,X23)|r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_13, plain, (v2_struct_0(X1)|v2_struct_0(X2)|u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_18, plain, (X1=esk2_4(X1,X2,X3,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (u1_struct_0(k4_waybel_9(esk3_0,esk4_0,X1))=a_3_0_waybel_9(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_23, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X3))|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (esk2_4(X1,esk3_0,esk4_0,X2)=X1|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0)),u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0))=a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_4(X1,esk3_0,esk4_0,X2),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (esk2_4(X1,esk3_0,esk4_0,esk5_0)=X1|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26])).
% 0.20/0.40  fof(c_0_30, plain, ![X16, X17]:(~l1_struct_0(X16)|(~l1_waybel_0(X17,X16)|l1_orders_2(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.40  fof(c_0_31, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_4(X1,esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0)=esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.40  fof(c_0_34, plain, ![X15]:(~l1_orders_2(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.40  cnf(c_0_35, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_36, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.40  cnf(c_0_37, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_33])).
% 0.20/0.40  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (l1_orders_2(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_14]), c_0_15])])).
% 0.20/0.40  cnf(c_0_41, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_16])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (~r1_tarski(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_19, c_0_26])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 31
% 0.20/0.40  # Proof object formula steps           : 17
% 0.20/0.40  # Proof object conjectures             : 25
% 0.20/0.40  # Proof object clause conjectures      : 22
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 15
% 0.20/0.40  # Proof object initial formulas used   : 8
% 0.20/0.40  # Proof object generating inferences   : 14
% 0.20/0.40  # Proof object simplifying inferences  : 22
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 8
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 18
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 18
% 0.20/0.40  # Processed clauses                    : 55
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 0
% 0.20/0.40  # ...remaining for further processing  : 54
% 0.20/0.40  # Other redundant clauses eliminated   : 1
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 4
% 0.20/0.40  # Generated clauses                    : 33
% 0.20/0.40  # ...of the previous two non-trivial   : 33
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 32
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 1
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 31
% 0.20/0.40  #    Positive orientable unit clauses  : 11
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 17
% 0.20/0.40  # Current number of unprocessed clauses: 13
% 0.20/0.40  # ...number of literals in the above   : 45
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 22
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 250
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 17
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 9
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 4
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 2255
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.012 s
% 0.20/0.40  # Total time               : 0.061 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
