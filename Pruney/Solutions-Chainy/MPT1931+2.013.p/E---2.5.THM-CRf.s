%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  228 ( 410 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X22)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r2_waybel_0(X37,X38,X39)
        | ~ r1_waybel_0(X37,X38,k6_subset_1(u1_struct_0(X37),X39))
        | v2_struct_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) )
      & ( r1_waybel_0(X37,X38,k6_subset_1(u1_struct_0(X37),X39))
        | r2_waybel_0(X37,X38,X39)
        | v2_struct_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] : k6_subset_1(X27,X28) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ r1_waybel_0(X40,X41,X42)
        | r1_waybel_0(X40,X41,X43)
        | ~ r1_tarski(X42,X43)
        | v2_struct_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | v2_struct_0(X40)
        | ~ l1_struct_0(X40) )
      & ( ~ r2_waybel_0(X40,X41,X42)
        | r2_waybel_0(X40,X41,X43)
        | ~ r1_tarski(X42,X43)
        | v2_struct_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | v2_struct_0(X40)
        | ~ l1_struct_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_16,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X29,X30,X31,X32,X34,X36] :
      ( ( m1_subset_1(esk5_4(X29,X30,X31,X32),u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ r2_waybel_0(X29,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29) )
      & ( r1_orders_2(X30,X32,esk5_4(X29,X30,X31,X32))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ r2_waybel_0(X29,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29) )
      & ( r2_hidden(k2_waybel_0(X29,X30,esk5_4(X29,X30,X31,X32)),X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ r2_waybel_0(X29,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29) )
      & ( m1_subset_1(esk6_3(X29,X30,X34),u1_struct_0(X30))
        | r2_waybel_0(X29,X30,X34)
        | v2_struct_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X30))
        | ~ r1_orders_2(X30,esk6_3(X29,X30,X34),X36)
        | ~ r2_hidden(k2_waybel_0(X29,X30,X36),X34)
        | r2_waybel_0(X29,X30,X34)
        | v2_struct_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_22,plain,
    ( r1_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,negated_conjecture,(
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

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk5_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X25] : m1_subset_1(esk4_1(X25),X25) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_30,plain,
    ( r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_struct_0(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & ~ r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X2,X1,X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36]),c_0_37])]),c_0_39]),c_0_40])).

cnf(c_0_45,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_43,c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:43:52 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.40  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.13/0.40  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.13/0.40  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.13/0.40  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.40  fof(c_0_10, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk3_3(X21,X22,X23),X23)|(~r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk3_3(X21,X22,X23),X22)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.40  fof(c_0_11, plain, ![X37, X38, X39]:((~r2_waybel_0(X37,X38,X39)|~r1_waybel_0(X37,X38,k6_subset_1(u1_struct_0(X37),X39))|(v2_struct_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~l1_struct_0(X37)))&(r1_waybel_0(X37,X38,k6_subset_1(u1_struct_0(X37),X39))|r2_waybel_0(X37,X38,X39)|(v2_struct_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~l1_struct_0(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.13/0.40  fof(c_0_12, plain, ![X27, X28]:k6_subset_1(X27,X28)=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  fof(c_0_14, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X40, X41, X42, X43]:((~r1_waybel_0(X40,X41,X42)|r1_waybel_0(X40,X41,X43)|~r1_tarski(X42,X43)|(v2_struct_0(X41)|~l1_waybel_0(X41,X40))|(v2_struct_0(X40)|~l1_struct_0(X40)))&(~r2_waybel_0(X40,X41,X42)|r2_waybel_0(X40,X41,X43)|~r1_tarski(X42,X43)|(v2_struct_0(X41)|~l1_waybel_0(X41,X40))|(v2_struct_0(X40)|~l1_struct_0(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.13/0.40  cnf(c_0_16, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_17, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  fof(c_0_20, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_21, plain, ![X29, X30, X31, X32, X34, X36]:((((m1_subset_1(esk5_4(X29,X30,X31,X32),u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|~r2_waybel_0(X29,X30,X31)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~l1_struct_0(X29)))&(r1_orders_2(X30,X32,esk5_4(X29,X30,X31,X32))|~m1_subset_1(X32,u1_struct_0(X30))|~r2_waybel_0(X29,X30,X31)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~l1_struct_0(X29))))&(r2_hidden(k2_waybel_0(X29,X30,esk5_4(X29,X30,X31,X32)),X31)|~m1_subset_1(X32,u1_struct_0(X30))|~r2_waybel_0(X29,X30,X31)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~l1_struct_0(X29))))&((m1_subset_1(esk6_3(X29,X30,X34),u1_struct_0(X30))|r2_waybel_0(X29,X30,X34)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~l1_struct_0(X29)))&(~m1_subset_1(X36,u1_struct_0(X30))|~r1_orders_2(X30,esk6_3(X29,X30,X34),X36)|~r2_hidden(k2_waybel_0(X29,X30,X36),X34)|r2_waybel_0(X29,X30,X34)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~l1_struct_0(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.13/0.40  cnf(c_0_22, plain, (r1_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_23, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  fof(c_0_26, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.18/0.40  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.40  cnf(c_0_28, plain, (r2_hidden(k2_waybel_0(X1,X2,esk5_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.40  fof(c_0_29, plain, ![X25]:m1_subset_1(esk4_1(X25),X25), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.18/0.40  cnf(c_0_30, plain, (r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.40  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.40  fof(c_0_32, negated_conjecture, ((~v2_struct_0(esk7_0)&l1_struct_0(esk7_0))&((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&l1_waybel_0(esk8_0,esk7_0))&~r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).
% 0.18/0.40  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X2,X1,X3)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.40  cnf(c_0_34, plain, (m1_subset_1(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.40  cnf(c_0_35, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.40  cnf(c_0_36, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_37, negated_conjecture, (l1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_38, negated_conjecture, (~r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.40  cnf(c_0_42, negated_conjecture, (r2_waybel_0(esk7_0,esk8_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_38]), c_0_39]), c_0_40])).
% 0.18/0.40  cnf(c_0_43, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.40  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36]), c_0_37])]), c_0_39]), c_0_40])).
% 0.18/0.40  cnf(c_0_45, plain, ($false), inference(sr,[status(thm)],[c_0_43, c_0_44]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 46
% 0.18/0.40  # Proof object clause steps            : 26
% 0.18/0.40  # Proof object formula steps           : 20
% 0.18/0.40  # Proof object conjectures             : 10
% 0.18/0.40  # Proof object clause conjectures      : 7
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 15
% 0.18/0.40  # Proof object initial formulas used   : 10
% 0.18/0.40  # Proof object generating inferences   : 8
% 0.18/0.40  # Proof object simplifying inferences  : 13
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 10
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 30
% 0.18/0.40  # Removed in clause preprocessing      : 1
% 0.18/0.40  # Initial clauses in saturation        : 29
% 0.18/0.40  # Processed clauses                    : 724
% 0.18/0.40  # ...of these trivial                  : 2
% 0.18/0.40  # ...subsumed                          : 553
% 0.18/0.40  # ...remaining for further processing  : 169
% 0.18/0.40  # Other redundant clauses eliminated   : 3
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 7
% 0.18/0.40  # Backward-rewritten                   : 9
% 0.18/0.40  # Generated clauses                    : 3331
% 0.18/0.40  # ...of the previous two non-trivial   : 2096
% 0.18/0.40  # Contextual simplify-reflections      : 3
% 0.18/0.40  # Paramodulations                      : 3316
% 0.18/0.40  # Factorizations                       : 6
% 0.18/0.40  # Equation resolutions                 : 3
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 144
% 0.18/0.40  #    Positive orientable unit clauses  : 19
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 6
% 0.18/0.40  #    Non-unit-clauses                  : 119
% 0.18/0.40  # Current number of unprocessed clauses: 1341
% 0.18/0.40  # ...number of literals in the above   : 4107
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 23
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 6143
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 4656
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 480
% 0.18/0.40  # Unit Clause-clause subsumption calls : 439
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 36
% 0.18/0.40  # BW rewrite match successes           : 5
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 35409
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.072 s
% 0.18/0.40  # System time              : 0.006 s
% 0.18/0.40  # Total time               : 0.078 s
% 0.18/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
