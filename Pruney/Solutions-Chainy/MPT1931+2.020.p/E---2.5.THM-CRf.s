%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:14 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 131 expanded)
%              Number of clauses        :   35 (  53 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  259 ( 647 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   19 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(existence_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ? [X2] : l1_waybel_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r2_waybel_0(X38,X39,X40)
        | ~ r1_waybel_0(X38,X39,k6_subset_1(u1_struct_0(X38),X40))
        | v2_struct_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ l1_struct_0(X38) )
      & ( r1_waybel_0(X38,X39,k6_subset_1(u1_struct_0(X38),X40))
        | r2_waybel_0(X38,X39,X40)
        | v2_struct_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ l1_struct_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_17,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ r1_waybel_0(X41,X42,X43)
        | r1_waybel_0(X41,X42,X44)
        | ~ r1_tarski(X43,X44)
        | v2_struct_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) )
      & ( ~ r2_waybel_0(X41,X42,X43)
        | r2_waybel_0(X41,X42,X44)
        | ~ r1_tarski(X43,X44)
        | v2_struct_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_22,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | ~ r1_tarski(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,plain,
    ( r1_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,negated_conjecture,(
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

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X26,X27,X28,X29,X31,X33] :
      ( ( m1_subset_1(esk3_4(X26,X27,X28,X29),u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r1_orders_2(X27,X29,esk3_4(X26,X27,X28,X29))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r2_hidden(k2_waybel_0(X26,X27,esk3_4(X26,X27,X28,X29)),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( m1_subset_1(esk4_3(X26,X27,X31),u1_struct_0(X27))
        | r2_waybel_0(X26,X27,X31)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X27))
        | ~ r1_orders_2(X27,esk4_3(X26,X27,X31),X33)
        | ~ r2_hidden(k2_waybel_0(X26,X27,X33),X31)
        | r2_waybel_0(X26,X27,X31)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_34,plain,
    ( r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

fof(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

fof(c_0_37,plain,(
    ! [X34,X35] :
      ( ~ l1_struct_0(X34)
      | ~ l1_waybel_0(X35,X34)
      | l1_orders_2(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X25] :
      ( ~ l1_orders_2(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_47,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X4,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43]),c_0_44]),c_0_45])).

fof(c_0_50,plain,(
    ! [X45,X46] :
      ( v2_struct_0(X45)
      | ~ l1_struct_0(X45)
      | ~ l1_waybel_0(X46,X45)
      | m1_subset_1(k4_yellow_6(X45,X46),u1_struct_0(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_51,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_42])])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_41]),c_0_42])]),c_0_45]),c_0_44])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_56,plain,(
    ! [X36] :
      ( ~ l1_struct_0(X36)
      | l1_waybel_0(esk5_1(X36),X36) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_l1_waybel_0])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ l1_waybel_0(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_44])).

cnf(c_0_58,plain,
    ( l1_waybel_0(esk5_1(X1),X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.018 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.12/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.12/0.37  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.12/0.37  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.12/0.37  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.12/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.12/0.37  fof(dt_k4_yellow_6, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_struct_0(X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 0.12/0.37  fof(existence_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>?[X2]:l1_waybel_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_l1_waybel_0)).
% 0.12/0.37  fof(c_0_12, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k4_xboole_0(X12,X13)))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|(~r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X18))|X19=k4_xboole_0(X17,X18))&((r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))&(~r2_hidden(esk2_3(X17,X18,X19),X18)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.37  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_14, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_16, plain, ![X38, X39, X40]:((~r2_waybel_0(X38,X39,X40)|~r1_waybel_0(X38,X39,k6_subset_1(u1_struct_0(X38),X40))|(v2_struct_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~l1_struct_0(X38)))&(r1_waybel_0(X38,X39,k6_subset_1(u1_struct_0(X38),X40))|r2_waybel_0(X38,X39,X40)|(v2_struct_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~l1_struct_0(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X21, X22]:k6_subset_1(X21,X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.12/0.37  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.37  fof(c_0_21, plain, ![X41, X42, X43, X44]:((~r1_waybel_0(X41,X42,X43)|r1_waybel_0(X41,X42,X44)|~r1_tarski(X43,X44)|(v2_struct_0(X42)|~l1_waybel_0(X42,X41))|(v2_struct_0(X41)|~l1_struct_0(X41)))&(~r2_waybel_0(X41,X42,X43)|r2_waybel_0(X41,X42,X44)|~r1_tarski(X43,X44)|(v2_struct_0(X42)|~l1_waybel_0(X42,X41))|(v2_struct_0(X41)|~l1_struct_0(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.12/0.37  cnf(c_0_22, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_24, plain, ![X23, X24]:(~r2_hidden(X23,X24)|~r1_tarski(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.12/0.37  cnf(c_0_27, plain, (r1_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_28, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_30, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.12/0.37  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  fof(c_0_33, plain, ![X26, X27, X28, X29, X31, X33]:((((m1_subset_1(esk3_4(X26,X27,X28,X29),u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26)))&(r1_orders_2(X27,X29,esk3_4(X26,X27,X28,X29))|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))&(r2_hidden(k2_waybel_0(X26,X27,esk3_4(X26,X27,X28,X29)),X28)|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))&((m1_subset_1(esk4_3(X26,X27,X31),u1_struct_0(X27))|r2_waybel_0(X26,X27,X31)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26)))&(~m1_subset_1(X33,u1_struct_0(X27))|~r1_orders_2(X27,esk4_3(X26,X27,X31),X33)|~r2_hidden(k2_waybel_0(X26,X27,X33),X31)|r2_waybel_0(X26,X27,X31)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.12/0.37  cnf(c_0_34, plain, (r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,X4)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.12/0.37  fof(c_0_36, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.12/0.37  fof(c_0_37, plain, ![X34, X35]:(~l1_struct_0(X34)|(~l1_waybel_0(X35,X34)|l1_orders_2(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.12/0.37  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.37  cnf(c_0_39, plain, (r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_40, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  fof(c_0_46, plain, ![X25]:(~l1_orders_2(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.12/0.37  cnf(c_0_47, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_waybel_0(X1,X2,k4_xboole_0(X4,X4))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43]), c_0_44]), c_0_45])).
% 0.12/0.37  fof(c_0_50, plain, ![X45, X46]:(v2_struct_0(X45)|~l1_struct_0(X45)|~l1_waybel_0(X46,X45)|m1_subset_1(k4_yellow_6(X45,X46),u1_struct_0(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).
% 0.12/0.37  cnf(c_0_51, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (l1_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_42])])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_41]), c_0_42])]), c_0_45]), c_0_44])).
% 0.12/0.37  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  fof(c_0_56, plain, ![X36]:(~l1_struct_0(X36)|l1_waybel_0(esk5_1(X36),X36)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_l1_waybel_0])])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (~l1_waybel_0(X1,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_44])).
% 0.12/0.37  cnf(c_0_58, plain, (l1_waybel_0(esk5_1(X1),X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_55])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 60
% 0.12/0.37  # Proof object clause steps            : 35
% 0.12/0.37  # Proof object formula steps           : 25
% 0.12/0.37  # Proof object conjectures             : 14
% 0.12/0.37  # Proof object clause conjectures      : 11
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 12
% 0.12/0.37  # Proof object generating inferences   : 16
% 0.12/0.37  # Proof object simplifying inferences  : 18
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 12
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 31
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 30
% 0.12/0.37  # Processed clauses                    : 152
% 0.12/0.37  # ...of these trivial                  : 2
% 0.12/0.37  # ...subsumed                          : 48
% 0.12/0.37  # ...remaining for further processing  : 102
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 246
% 0.12/0.37  # ...of the previous two non-trivial   : 191
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 235
% 0.12/0.37  # Factorizations                       : 6
% 0.12/0.37  # Equation resolutions                 : 5
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
% 0.12/0.37  # Current number of processed clauses  : 71
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 8
% 0.12/0.37  #    Non-unit-clauses                  : 51
% 0.12/0.37  # Current number of unprocessed clauses: 99
% 0.12/0.37  # ...number of literals in the above   : 360
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 1240
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 211
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 25
% 0.12/0.37  # Unit Clause-clause subsumption calls : 87
% 0.12/0.37  # Rewrite failures with RHS unbound    : 24
% 0.12/0.37  # BW rewrite match attempts            : 42
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 5910
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.022 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.028 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
