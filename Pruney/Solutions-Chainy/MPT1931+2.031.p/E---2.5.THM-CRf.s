%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:15 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 114 expanded)
%              Number of clauses        :   30 (  45 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 725 expanded)
%              Number of equality atoms :   18 (  65 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

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

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(dt_o_2_2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r2_waybel_0(X25,X26,X27)
        | ~ r1_waybel_0(X25,X26,k6_subset_1(u1_struct_0(X25),X27))
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( r1_waybel_0(X25,X26,k6_subset_1(u1_struct_0(X25),X27))
        | r2_waybel_0(X25,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X22,X24] :
      ( ( m1_subset_1(esk2_4(X17,X18,X19,X20),u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ r2_waybel_0(X17,X18,X19)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( r1_orders_2(X18,X20,esk2_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ r2_waybel_0(X17,X18,X19)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( r2_hidden(k2_waybel_0(X17,X18,esk2_4(X17,X18,X19,X20)),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ r2_waybel_0(X17,X18,X19)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( m1_subset_1(esk3_3(X17,X18,X22),u1_struct_0(X18))
        | r2_waybel_0(X17,X18,X22)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X18))
        | ~ r1_orders_2(X18,esk3_3(X17,X18,X22),X24)
        | ~ r2_hidden(k2_waybel_0(X17,X18,X24),X22)
        | r2_waybel_0(X17,X18,X22)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

cnf(c_0_21,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v4_orders_2(esk5_0)
    & v7_waybel_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & ~ r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X4,X5))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X4,X5),X3)),X5) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X3,X4),X5)),X3)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_28,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,k4_xboole_0(X3,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_waybel_0(X2,X1,k4_xboole_0(X4,X4))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_0(esk4_0,esk5_0,k4_xboole_0(X1,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31]),c_0_32]),c_0_33])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | m1_subset_1(o_2_2_yellow_6(X28,X29),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_2_yellow_6])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29]),c_0_30])]),c_0_33]),c_0_32])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( v7_waybel_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_30])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n016.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 18:49:19 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.15/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.43  #
% 0.15/0.43  # Preprocessing time       : 0.028 s
% 0.15/0.43  # Presaturation interreduction done
% 0.15/0.43  
% 0.15/0.43  # Proof found!
% 0.15/0.43  # SZS status Theorem
% 0.15/0.43  # SZS output start CNFRefutation
% 0.15/0.43  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.15/0.43  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.15/0.43  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.15/0.43  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.15/0.43  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.15/0.43  fof(dt_o_2_2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 0.15/0.43  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.15/0.43  cnf(c_0_7, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.43  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.43  cnf(c_0_9, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.43  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_7])).
% 0.15/0.43  fof(c_0_11, plain, ![X25, X26, X27]:((~r2_waybel_0(X25,X26,X27)|~r1_waybel_0(X25,X26,k6_subset_1(u1_struct_0(X25),X27))|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25)))&(r1_waybel_0(X25,X26,k6_subset_1(u1_struct_0(X25),X27))|r2_waybel_0(X25,X26,X27)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.15/0.43  fof(c_0_12, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.15/0.43  cnf(c_0_13, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.15/0.43  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.15/0.43  fof(c_0_15, plain, ![X17, X18, X19, X20, X22, X24]:((((m1_subset_1(esk2_4(X17,X18,X19,X20),u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~r2_waybel_0(X17,X18,X19)|(v2_struct_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~l1_struct_0(X17)))&(r1_orders_2(X18,X20,esk2_4(X17,X18,X19,X20))|~m1_subset_1(X20,u1_struct_0(X18))|~r2_waybel_0(X17,X18,X19)|(v2_struct_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~l1_struct_0(X17))))&(r2_hidden(k2_waybel_0(X17,X18,esk2_4(X17,X18,X19,X20)),X19)|~m1_subset_1(X20,u1_struct_0(X18))|~r2_waybel_0(X17,X18,X19)|(v2_struct_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~l1_struct_0(X17))))&((m1_subset_1(esk3_3(X17,X18,X22),u1_struct_0(X18))|r2_waybel_0(X17,X18,X22)|(v2_struct_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~l1_struct_0(X17)))&(~m1_subset_1(X24,u1_struct_0(X18))|~r1_orders_2(X18,esk3_3(X17,X18,X22),X24)|~r2_hidden(k2_waybel_0(X17,X18,X24),X22)|r2_waybel_0(X17,X18,X22)|(v2_struct_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~l1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.15/0.43  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.43  cnf(c_0_17, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.43  cnf(c_0_18, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.43  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.43  fof(c_0_20, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.15/0.43  cnf(c_0_21, plain, (r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.43  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.15/0.43  cnf(c_0_23, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.43  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.15/0.43  fof(c_0_25, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((((~v2_struct_0(esk5_0)&v4_orders_2(esk5_0))&v7_waybel_0(esk5_0))&l1_waybel_0(esk5_0,esk4_0))&~r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.15/0.43  cnf(c_0_26, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_waybel_0(X1,X2,k4_xboole_0(X4,X5))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X4,X5),X3)),X5)), inference(spm,[status(thm)],[c_0_13, c_0_21])).
% 0.15/0.43  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X3,X4),X5)),X3)|~m1_subset_1(X5,u1_struct_0(X2))|~r2_waybel_0(X1,X2,k4_xboole_0(X3,X4))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.15/0.43  cnf(c_0_28, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,k4_xboole_0(X3,u1_struct_0(X1)))|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.43  cnf(c_0_29, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_30, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_31, negated_conjecture, (~r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_waybel_0(X2,X1,k4_xboole_0(X4,X4))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.43  cnf(c_0_35, negated_conjecture, (r2_waybel_0(esk4_0,esk5_0,k4_xboole_0(X1,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31]), c_0_32]), c_0_33])).
% 0.15/0.43  fof(c_0_36, plain, ![X28, X29]:(v2_struct_0(X28)|~l1_struct_0(X28)|v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|m1_subset_1(o_2_2_yellow_6(X28,X29),u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_2_yellow_6])])])).
% 0.15/0.43  cnf(c_0_37, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29]), c_0_30])]), c_0_33]), c_0_32])).
% 0.15/0.43  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.43  cnf(c_0_39, negated_conjecture, (v7_waybel_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_40, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.43  cnf(c_0_41, negated_conjecture, (v2_struct_0(X1)|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])]), c_0_33])).
% 0.15/0.43  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_30])]), c_0_32]), ['proof']).
% 0.15/0.43  # SZS output end CNFRefutation
% 0.15/0.43  # Proof object total steps             : 43
% 0.15/0.43  # Proof object clause steps            : 30
% 0.15/0.43  # Proof object formula steps           : 13
% 0.15/0.43  # Proof object conjectures             : 14
% 0.15/0.43  # Proof object clause conjectures      : 11
% 0.15/0.43  # Proof object formula conjectures     : 3
% 0.15/0.43  # Proof object initial clauses used    : 15
% 0.15/0.43  # Proof object initial formulas used   : 6
% 0.15/0.43  # Proof object generating inferences   : 14
% 0.15/0.43  # Proof object simplifying inferences  : 19
% 0.15/0.43  # Training examples: 0 positive, 0 negative
% 0.15/0.43  # Parsed axioms                        : 6
% 0.15/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.43  # Initial clauses                      : 22
% 0.15/0.43  # Removed in clause preprocessing      : 1
% 0.15/0.43  # Initial clauses in saturation        : 21
% 0.15/0.43  # Processed clauses                    : 1619
% 0.15/0.43  # ...of these trivial                  : 32
% 0.15/0.43  # ...subsumed                          : 1410
% 0.15/0.43  # ...remaining for further processing  : 177
% 0.15/0.43  # Other redundant clauses eliminated   : 25
% 0.15/0.43  # Clauses deleted for lack of memory   : 0
% 0.15/0.43  # Backward-subsumed                    : 2
% 0.15/0.43  # Backward-rewritten                   : 0
% 0.15/0.43  # Generated clauses                    : 6847
% 0.15/0.43  # ...of the previous two non-trivial   : 5656
% 0.15/0.43  # Contextual simplify-reflections      : 5
% 0.15/0.43  # Paramodulations                      : 6797
% 0.15/0.43  # Factorizations                       : 14
% 0.15/0.43  # Equation resolutions                 : 36
% 0.15/0.43  # Propositional unsat checks           : 0
% 0.15/0.43  #    Propositional check models        : 0
% 0.15/0.43  #    Propositional check unsatisfiable : 0
% 0.15/0.43  #    Propositional clauses             : 0
% 0.15/0.43  #    Propositional clauses after purity: 0
% 0.15/0.43  #    Propositional unsat core size     : 0
% 0.15/0.43  #    Propositional preprocessing time  : 0.000
% 0.15/0.43  #    Propositional encoding time       : 0.000
% 0.15/0.43  #    Propositional solver time         : 0.000
% 0.15/0.43  #    Success case prop preproc time    : 0.000
% 0.15/0.43  #    Success case prop encoding time   : 0.000
% 0.15/0.43  #    Success case prop solver time     : 0.000
% 0.15/0.43  # Current number of processed clauses  : 154
% 0.15/0.43  #    Positive orientable unit clauses  : 25
% 0.15/0.43  #    Positive unorientable unit clauses: 5
% 0.15/0.43  #    Negative unit clauses             : 11
% 0.15/0.43  #    Non-unit-clauses                  : 113
% 0.15/0.43  # Current number of unprocessed clauses: 4079
% 0.15/0.43  # ...number of literals in the above   : 12622
% 0.15/0.43  # Current number of archived formulas  : 0
% 0.15/0.43  # Current number of archived clauses   : 24
% 0.15/0.43  # Clause-clause subsumption calls (NU) : 7999
% 0.15/0.43  # Rec. Clause-clause subsumption calls : 4694
% 0.15/0.43  # Non-unit clause-clause subsumptions  : 692
% 0.15/0.43  # Unit Clause-clause subsumption calls : 414
% 0.15/0.43  # Rewrite failures with RHS unbound    : 225
% 0.15/0.43  # BW rewrite match attempts            : 432
% 0.15/0.43  # BW rewrite match successes           : 35
% 0.15/0.43  # Condensation attempts                : 0
% 0.15/0.43  # Condensation successes               : 0
% 0.15/0.43  # Termbank termtop insertions          : 78284
% 0.15/0.43  
% 0.15/0.43  # -------------------------------------------------
% 0.15/0.43  # User time                : 0.123 s
% 0.15/0.43  # System time              : 0.009 s
% 0.15/0.43  # Total time               : 0.132 s
% 0.15/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
