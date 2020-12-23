%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 183 expanded)
%              Number of clauses        :   31 (  66 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 840 expanded)
%              Number of equality atoms :   12 (  25 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d1_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v2_struct_0(X1)
      <=> v1_xboole_0(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

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

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
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

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk3_0,esk4_0,X1)) = a_3_0_waybel_9(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)) = a_3_0_waybel_9(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk3_0,esk4_0,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ l1_struct_0(X15)
      | ~ l1_waybel_0(X16,X15)
      | l1_orders_2(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_27,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_31,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = esk2_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X17] :
      ( ( ~ v2_struct_0(X17)
        | v1_xboole_0(u1_struct_0(X17))
        | ~ l1_struct_0(X17) )
      & ( ~ v1_xboole_0(u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_12]),c_0_13])])).

cnf(c_0_38,negated_conjecture,
    ( esk2_4(X1,esk3_0,esk4_0,X2) = X1
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk2_4(X1,esk3_0,esk4_0,esk5_0) = X1
    | ~ r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0) = esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.19/0.37  fof(t12_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_waybel_9)).
% 0.19/0.37  fof(fraenkel_a_3_0_waybel_9, axiom, ![X1, X2, X3, X4]:(((((~(v2_struct_0(X2))&l1_struct_0(X2))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X2))&m1_subset_1(X4,u1_struct_0(X3)))=>(r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))<=>?[X5]:((m1_subset_1(X5,u1_struct_0(X3))&X1=X5)&r1_orders_2(X3,X4,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.37  fof(d1_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>(v2_struct_0(X1)<=>v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.19/0.37  fof(c_0_9, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~l1_struct_0(X24)|(v2_struct_0(X25)|~l1_waybel_0(X25,X24)|(~m1_subset_1(X26,u1_struct_0(X25))|u1_struct_0(k4_waybel_9(X24,X25,X26))=a_3_0_waybel_9(X24,X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_waybel_9])])])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&((~v2_struct_0(esk4_0)&l1_waybel_0(esk4_0,esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|v2_struct_0(X2)|u1_struct_0(k4_waybel_9(X1,X2,X3))=a_3_0_waybel_9(X1,X2,X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_16, plain, ![X18, X19, X20, X21, X23]:((((m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X20))|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20))))&(X18=esk2_4(X18,X19,X20,X21)|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20)))))&(r1_orders_2(X20,X21,esk2_4(X18,X19,X20,X21))|~r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20)))))&(~m1_subset_1(X23,u1_struct_0(X20))|X18!=X23|~r1_orders_2(X20,X21,X23)|r2_hidden(X18,a_3_0_waybel_9(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v2_struct_0(X20)|~l1_waybel_0(X20,X19)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (u1_struct_0(k4_waybel_9(esk3_0,esk4_0,X1))=a_3_0_waybel_9(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_19, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X3))|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (u1_struct_0(k4_waybel_9(esk3_0,esk4_0,esk5_0))=a_3_0_waybel_9(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  fof(c_0_22, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_4(X1,esk3_0,esk4_0,X2),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (~r1_tarski(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  fof(c_0_26, plain, ![X15, X16]:(~l1_struct_0(X15)|(~l1_waybel_0(X16,X15)|l1_orders_2(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.19/0.37  fof(c_0_27, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_4(X1,esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  fof(c_0_30, plain, ![X14]:(~l1_orders_2(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.37  cnf(c_0_31, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_32, plain, (X1=esk2_4(X1,X2,X3,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))|~l1_struct_0(X2)|~l1_waybel_0(X3,X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_33, plain, ![X17]:((~v2_struct_0(X17)|v1_xboole_0(u1_struct_0(X17))|~l1_struct_0(X17))&(~v1_xboole_0(u1_struct_0(X17))|v2_struct_0(X17)|~l1_struct_0(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).
% 0.19/0.37  cnf(c_0_34, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (l1_orders_2(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_12]), c_0_13])])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (esk2_4(X1,esk3_0,esk4_0,X2)=X1|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.19/0.37  cnf(c_0_39, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (esk2_4(X1,esk3_0,esk4_0,esk5_0)=X1|~r2_hidden(X1,a_3_0_waybel_9(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_18])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), c_0_14])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (esk2_4(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),esk3_0,esk4_0,esk5_0)=esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.19/0.37  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(a_3_0_waybel_9(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 48
% 0.19/0.37  # Proof object clause steps            : 31
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 25
% 0.19/0.37  # Proof object clause conjectures      : 22
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 14
% 0.19/0.37  # Proof object simplifying inferences  : 20
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 19
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 19
% 0.19/0.37  # Processed clauses                    : 66
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 65
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 57
% 0.19/0.37  # ...of the previous two non-trivial   : 54
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 56
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
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
% 0.19/0.37  # Current number of processed clauses  : 39
% 0.19/0.37  #    Positive orientable unit clauses  : 11
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 25
% 0.19/0.37  # Current number of unprocessed clauses: 24
% 0.19/0.37  # ...number of literals in the above   : 58
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 25
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 437
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 93
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 20
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 6
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2901
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
