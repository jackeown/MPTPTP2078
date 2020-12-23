%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 325 expanded)
%              Number of clauses        :   45 ( 153 expanded)
%              Number of leaves         :   10 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (1724 expanded)
%              Number of equality atoms :   19 ( 236 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   2 average)
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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk3_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_23,plain,(
    ! [X42,X43,X44] :
      ( ( ~ r2_waybel_0(X42,X43,X44)
        | ~ r1_waybel_0(X42,X43,k6_subset_1(u1_struct_0(X42),X44))
        | v2_struct_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | v2_struct_0(X42)
        | ~ l1_struct_0(X42) )
      & ( r1_waybel_0(X42,X43,k6_subset_1(u1_struct_0(X42),X44))
        | r2_waybel_0(X42,X43,X44)
        | v2_struct_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | v2_struct_0(X42)
        | ~ l1_struct_0(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_24,plain,(
    ! [X30,X31] : k6_subset_1(X30,X31) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_25,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ r1_waybel_0(X45,X46,X47)
        | r1_waybel_0(X45,X46,X48)
        | ~ r1_tarski(X47,X48)
        | v2_struct_0(X46)
        | ~ l1_waybel_0(X46,X45)
        | v2_struct_0(X45)
        | ~ l1_struct_0(X45) )
      & ( ~ r2_waybel_0(X45,X46,X47)
        | r2_waybel_0(X45,X46,X48)
        | ~ r1_tarski(X47,X48)
        | v2_struct_0(X46)
        | ~ l1_waybel_0(X46,X45)
        | v2_struct_0(X45)
        | ~ l1_struct_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_29,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

fof(c_0_37,negated_conjecture,(
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

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_32])).

fof(c_0_39,plain,(
    ! [X34,X35,X36,X37,X39,X41] :
      ( ( m1_subset_1(esk4_4(X34,X35,X36,X37),u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ r2_waybel_0(X34,X35,X36)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( r1_orders_2(X35,X37,esk4_4(X34,X35,X36,X37))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ r2_waybel_0(X34,X35,X36)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( r2_hidden(k2_waybel_0(X34,X35,esk4_4(X34,X35,X36,X37)),X36)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ r2_waybel_0(X34,X35,X36)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( m1_subset_1(esk5_3(X34,X35,X39),u1_struct_0(X35))
        | r2_waybel_0(X34,X35,X39)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X35))
        | ~ r1_orders_2(X35,esk5_3(X34,X35,X39),X41)
        | ~ r2_hidden(k2_waybel_0(X34,X35,X41),X39)
        | r2_waybel_0(X34,X35,X39)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_40,plain,
    ( r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).

fof(c_0_43,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X26,X25)
        | r2_hidden(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ r2_hidden(X26,X25)
        | m1_subset_1(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ m1_subset_1(X26,X25)
        | v1_xboole_0(X26)
        | ~ v1_xboole_0(X25) )
      & ( ~ v1_xboole_0(X26)
        | m1_subset_1(X26,X25)
        | ~ v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_32]),c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),c_0_50]),c_0_51])).

fof(c_0_55,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | m1_subset_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k4_xboole_0(X2,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_47]),c_0_48])]),c_0_51]),c_0_50])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( m1_subset_1(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( m1_subset_1(k4_xboole_0(X1,X1),X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.029 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.55  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.20/0.55  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.55  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.20/0.55  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.20/0.55  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.20/0.55  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.55  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.55  fof(c_0_10, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk3_3(X21,X22,X23),X23)|(~r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk3_3(X21,X22,X23),X22)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.55  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  fof(c_0_12, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.55  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_14, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_15, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_16, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.55  cnf(c_0_17, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.55  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_20, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk3_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.55  cnf(c_0_21, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.55  cnf(c_0_22, plain, (r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)|v1_xboole_0(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.55  fof(c_0_23, plain, ![X42, X43, X44]:((~r2_waybel_0(X42,X43,X44)|~r1_waybel_0(X42,X43,k6_subset_1(u1_struct_0(X42),X44))|(v2_struct_0(X43)|~l1_waybel_0(X43,X42))|(v2_struct_0(X42)|~l1_struct_0(X42)))&(r1_waybel_0(X42,X43,k6_subset_1(u1_struct_0(X42),X44))|r2_waybel_0(X42,X43,X44)|(v2_struct_0(X43)|~l1_waybel_0(X43,X42))|(v2_struct_0(X42)|~l1_struct_0(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.20/0.55  fof(c_0_24, plain, ![X30, X31]:k6_subset_1(X30,X31)=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.55  fof(c_0_25, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.55  cnf(c_0_26, plain, (X1=k4_xboole_0(X2,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.55  cnf(c_0_27, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.55  fof(c_0_28, plain, ![X45, X46, X47, X48]:((~r1_waybel_0(X45,X46,X47)|r1_waybel_0(X45,X46,X48)|~r1_tarski(X47,X48)|(v2_struct_0(X46)|~l1_waybel_0(X46,X45))|(v2_struct_0(X45)|~l1_struct_0(X45)))&(~r2_waybel_0(X45,X46,X47)|r2_waybel_0(X45,X46,X48)|~r1_tarski(X47,X48)|(v2_struct_0(X46)|~l1_waybel_0(X46,X45))|(v2_struct_0(X45)|~l1_struct_0(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.20/0.55  cnf(c_0_29, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.55  cnf(c_0_30, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.55  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_32, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.55  cnf(c_0_33, plain, (r1_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.55  cnf(c_0_34, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.55  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.20/0.55  fof(c_0_37, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.20/0.55  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_32])).
% 0.20/0.55  fof(c_0_39, plain, ![X34, X35, X36, X37, X39, X41]:((((m1_subset_1(esk4_4(X34,X35,X36,X37),u1_struct_0(X35))|~m1_subset_1(X37,u1_struct_0(X35))|~r2_waybel_0(X34,X35,X36)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34)))&(r1_orders_2(X35,X37,esk4_4(X34,X35,X36,X37))|~m1_subset_1(X37,u1_struct_0(X35))|~r2_waybel_0(X34,X35,X36)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34))))&(r2_hidden(k2_waybel_0(X34,X35,esk4_4(X34,X35,X36,X37)),X36)|~m1_subset_1(X37,u1_struct_0(X35))|~r2_waybel_0(X34,X35,X36)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34))))&((m1_subset_1(esk5_3(X34,X35,X39),u1_struct_0(X35))|r2_waybel_0(X34,X35,X39)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34)))&(~m1_subset_1(X41,u1_struct_0(X35))|~r1_orders_2(X35,esk5_3(X34,X35,X39),X41)|~r2_hidden(k2_waybel_0(X34,X35,X41),X39)|r2_waybel_0(X34,X35,X39)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.20/0.55  cnf(c_0_40, plain, (r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,X4)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r1_tarski(k4_xboole_0(u1_struct_0(X1),X4),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.55  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.55  fof(c_0_42, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).
% 0.20/0.55  fof(c_0_43, plain, ![X25, X26]:(((~m1_subset_1(X26,X25)|r2_hidden(X26,X25)|v1_xboole_0(X25))&(~r2_hidden(X26,X25)|m1_subset_1(X26,X25)|v1_xboole_0(X25)))&((~m1_subset_1(X26,X25)|v1_xboole_0(X26)|~v1_xboole_0(X25))&(~v1_xboole_0(X26)|m1_subset_1(X26,X25)|~v1_xboole_0(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.55  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_32]), c_0_38])).
% 0.20/0.55  cnf(c_0_45, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_46, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.55  cnf(c_0_47, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_48, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_49, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_52, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.55  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.55  cnf(c_0_54, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49]), c_0_50]), c_0_51])).
% 0.20/0.55  fof(c_0_55, plain, ![X32, X33]:(~r2_hidden(X32,X33)|m1_subset_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.55  cnf(c_0_56, plain, (m1_subset_1(X1,k4_xboole_0(X2,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_27])).
% 0.20/0.55  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk3_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_15])).
% 0.20/0.55  cnf(c_0_58, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_47]), c_0_48])]), c_0_51]), c_0_50])).
% 0.20/0.55  cnf(c_0_59, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.55  cnf(c_0_60, plain, (m1_subset_1(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 0.20/0.55  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_57])).
% 0.20/0.55  cnf(c_0_62, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.55  cnf(c_0_63, plain, (m1_subset_1(k4_xboole_0(X1,X1),X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.55  cnf(c_0_64, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_17])).
% 0.20/0.55  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_58]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 66
% 0.20/0.55  # Proof object clause steps            : 45
% 0.20/0.55  # Proof object formula steps           : 21
% 0.20/0.55  # Proof object conjectures             : 13
% 0.20/0.55  # Proof object clause conjectures      : 10
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 19
% 0.20/0.55  # Proof object initial formulas used   : 10
% 0.20/0.55  # Proof object generating inferences   : 25
% 0.20/0.55  # Proof object simplifying inferences  : 13
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 11
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 34
% 0.20/0.55  # Removed in clause preprocessing      : 1
% 0.20/0.55  # Initial clauses in saturation        : 33
% 0.20/0.55  # Processed clauses                    : 2729
% 0.20/0.55  # ...of these trivial                  : 19
% 0.20/0.55  # ...subsumed                          : 2340
% 0.20/0.55  # ...remaining for further processing  : 370
% 0.20/0.55  # Other redundant clauses eliminated   : 46
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 19
% 0.20/0.55  # Backward-rewritten                   : 11
% 0.20/0.55  # Generated clauses                    : 12427
% 0.20/0.55  # ...of the previous two non-trivial   : 11479
% 0.20/0.55  # Contextual simplify-reflections      : 5
% 0.20/0.55  # Paramodulations                      : 12343
% 0.20/0.55  # Factorizations                       : 24
% 0.20/0.55  # Equation resolutions                 : 60
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 308
% 0.20/0.55  #    Positive orientable unit clauses  : 22
% 0.20/0.55  #    Positive unorientable unit clauses: 2
% 0.20/0.55  #    Negative unit clauses             : 10
% 0.20/0.55  #    Non-unit-clauses                  : 274
% 0.20/0.55  # Current number of unprocessed clauses: 8748
% 0.20/0.55  # ...number of literals in the above   : 46294
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 63
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 36054
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 15356
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 1924
% 0.20/0.55  # Unit Clause-clause subsumption calls : 1239
% 0.20/0.55  # Rewrite failures with RHS unbound    : 100
% 0.20/0.55  # BW rewrite match attempts            : 100
% 0.20/0.55  # BW rewrite match successes           : 21
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 168737
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.202 s
% 0.20/0.55  # System time              : 0.010 s
% 0.20/0.55  # Total time               : 0.213 s
% 0.20/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
