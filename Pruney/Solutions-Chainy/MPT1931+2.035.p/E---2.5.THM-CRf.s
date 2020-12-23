%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:16 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  92 expanded)
%              Number of clauses        :   29 (  39 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 487 expanded)
%              Number of equality atoms :   17 (  40 expanded)
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

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

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

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_9,plain,(
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

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X23,X24,X26] :
      ( ( r2_hidden(esk3_2(X23,X24),X24)
        | ~ r2_hidden(X23,X24) )
      & ( ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X26,esk3_2(X23,X24))
        | ~ r2_hidden(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_17,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_waybel_0(X39,X40,X41)
        | ~ r1_waybel_0(X39,X40,k6_subset_1(u1_struct_0(X39),X41))
        | v2_struct_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | v2_struct_0(X39)
        | ~ l1_struct_0(X39) )
      & ( r1_waybel_0(X39,X40,k6_subset_1(u1_struct_0(X39),X41))
        | r2_waybel_0(X39,X40,X41)
        | v2_struct_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | v2_struct_0(X39)
        | ~ l1_struct_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_18,plain,(
    ! [X29,X30] : k6_subset_1(X29,X30) = k4_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k4_xboole_0(X21,X22) = X21 )
      & ( k4_xboole_0(X21,X22) != X21
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,negated_conjecture,(
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

cnf(c_0_28,plain,
    ( ~ r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

fof(c_0_30,plain,(
    ! [X31,X32,X33,X34,X36,X38] :
      ( ( m1_subset_1(esk5_4(X31,X32,X33,X34),u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ r2_waybel_0(X31,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( r1_orders_2(X32,X34,esk5_4(X31,X32,X33,X34))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ r2_waybel_0(X31,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( r2_hidden(k2_waybel_0(X31,X32,esk5_4(X31,X32,X33,X34)),X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ r2_waybel_0(X31,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( m1_subset_1(esk6_3(X31,X32,X36),u1_struct_0(X32))
        | r2_waybel_0(X31,X32,X36)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X32))
        | ~ r1_orders_2(X32,esk6_3(X31,X32,X36),X38)
        | ~ r2_hidden(k2_waybel_0(X31,X32,X38),X36)
        | r2_waybel_0(X31,X32,X36)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_struct_0(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & ~ r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk5_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X2,X1,k4_xboole_0(X3,X3))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk8_0,k4_xboole_0(X1,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),c_0_39]),c_0_40]),c_0_41])).

fof(c_0_44,plain,(
    ! [X27] : m1_subset_1(esk4_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37]),c_0_38])]),c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:58:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.21/1.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 1.21/1.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.21/1.41  #
% 1.21/1.41  # Preprocessing time       : 0.029 s
% 1.21/1.41  
% 1.21/1.41  # Proof found!
% 1.21/1.41  # SZS status Theorem
% 1.21/1.41  # SZS output start CNFRefutation
% 1.21/1.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.21/1.41  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.21/1.41  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 1.21/1.41  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 1.21/1.41  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.21/1.41  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.21/1.41  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 1.21/1.41  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 1.21/1.41  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.21/1.41  fof(c_0_9, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.21/1.41  cnf(c_0_10, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.21/1.41  fof(c_0_11, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.21/1.41  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.21/1.41  cnf(c_0_13, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_10])).
% 1.21/1.41  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.21/1.41  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_12])).
% 1.21/1.41  fof(c_0_16, plain, ![X23, X24, X26]:((r2_hidden(esk3_2(X23,X24),X24)|~r2_hidden(X23,X24))&(~r2_hidden(X26,X24)|~r2_hidden(X26,esk3_2(X23,X24))|~r2_hidden(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 1.21/1.41  fof(c_0_17, plain, ![X39, X40, X41]:((~r2_waybel_0(X39,X40,X41)|~r1_waybel_0(X39,X40,k6_subset_1(u1_struct_0(X39),X41))|(v2_struct_0(X40)|~l1_waybel_0(X40,X39))|(v2_struct_0(X39)|~l1_struct_0(X39)))&(r1_waybel_0(X39,X40,k6_subset_1(u1_struct_0(X39),X41))|r2_waybel_0(X39,X40,X41)|(v2_struct_0(X40)|~l1_waybel_0(X40,X39))|(v2_struct_0(X39)|~l1_struct_0(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 1.21/1.41  fof(c_0_18, plain, ![X29, X30]:k6_subset_1(X29,X30)=k4_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.21/1.41  fof(c_0_19, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k4_xboole_0(X21,X22)=X21)&(k4_xboole_0(X21,X22)!=X21|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 1.21/1.41  cnf(c_0_20, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.21/1.41  cnf(c_0_21, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 1.21/1.41  cnf(c_0_22, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.21/1.41  cnf(c_0_23, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.21/1.41  cnf(c_0_24, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.21/1.41  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.21/1.41  cnf(c_0_26, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.21/1.41  fof(c_0_27, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 1.21/1.41  cnf(c_0_28, plain, (~r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X3)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_22])).
% 1.21/1.41  cnf(c_0_29, plain, (r2_hidden(esk3_2(X1,k4_xboole_0(X2,X3)),X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_22])).
% 1.21/1.41  fof(c_0_30, plain, ![X31, X32, X33, X34, X36, X38]:((((m1_subset_1(esk5_4(X31,X32,X33,X34),u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~r2_waybel_0(X31,X32,X33)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))&(r1_orders_2(X32,X34,esk5_4(X31,X32,X33,X34))|~m1_subset_1(X34,u1_struct_0(X32))|~r2_waybel_0(X31,X32,X33)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31))))&(r2_hidden(k2_waybel_0(X31,X32,esk5_4(X31,X32,X33,X34)),X33)|~m1_subset_1(X34,u1_struct_0(X32))|~r2_waybel_0(X31,X32,X33)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31))))&((m1_subset_1(esk6_3(X31,X32,X36),u1_struct_0(X32))|r2_waybel_0(X31,X32,X36)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))&(~m1_subset_1(X38,u1_struct_0(X32))|~r1_orders_2(X32,esk6_3(X31,X32,X36),X38)|~r2_hidden(k2_waybel_0(X31,X32,X38),X36)|r2_waybel_0(X31,X32,X36)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 1.21/1.41  cnf(c_0_31, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 1.21/1.41  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.21/1.41  fof(c_0_33, negated_conjecture, ((~v2_struct_0(esk7_0)&l1_struct_0(esk7_0))&((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&l1_waybel_0(esk8_0,esk7_0))&~r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).
% 1.21/1.41  cnf(c_0_34, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.21/1.41  cnf(c_0_35, plain, (r2_hidden(k2_waybel_0(X1,X2,esk5_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.21/1.41  cnf(c_0_36, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.21/1.41  cnf(c_0_37, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.21/1.41  cnf(c_0_38, negated_conjecture, (l1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.21/1.41  cnf(c_0_39, negated_conjecture, (~r1_waybel_0(esk7_0,esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.21/1.41  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.21/1.41  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.21/1.41  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X2,X1,k4_xboole_0(X3,X3))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.21/1.41  cnf(c_0_43, negated_conjecture, (r2_waybel_0(esk7_0,esk8_0,k4_xboole_0(X1,X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])]), c_0_39]), c_0_40]), c_0_41])).
% 1.21/1.41  fof(c_0_44, plain, ![X27]:m1_subset_1(esk4_1(X27),X27), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 1.21/1.41  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37]), c_0_38])]), c_0_40]), c_0_41])).
% 1.21/1.41  cnf(c_0_46, plain, (m1_subset_1(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.21/1.41  cnf(c_0_47, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['proof']).
% 1.21/1.41  # SZS output end CNFRefutation
% 1.21/1.41  # Proof object total steps             : 48
% 1.21/1.41  # Proof object clause steps            : 29
% 1.21/1.41  # Proof object formula steps           : 19
% 1.21/1.41  # Proof object conjectures             : 11
% 1.21/1.41  # Proof object clause conjectures      : 8
% 1.21/1.41  # Proof object formula conjectures     : 3
% 1.21/1.41  # Proof object initial clauses used    : 14
% 1.21/1.41  # Proof object initial formulas used   : 9
% 1.21/1.41  # Proof object generating inferences   : 12
% 1.21/1.41  # Proof object simplifying inferences  : 13
% 1.21/1.41  # Training examples: 0 positive, 0 negative
% 1.21/1.41  # Parsed axioms                        : 9
% 1.21/1.41  # Removed by relevancy pruning/SinE    : 0
% 1.21/1.41  # Initial clauses                      : 29
% 1.21/1.41  # Removed in clause preprocessing      : 1
% 1.21/1.41  # Initial clauses in saturation        : 28
% 1.21/1.41  # Processed clauses                    : 9651
% 1.21/1.41  # ...of these trivial                  : 976
% 1.21/1.41  # ...subsumed                          : 7943
% 1.21/1.41  # ...remaining for further processing  : 732
% 1.21/1.41  # Other redundant clauses eliminated   : 496
% 1.21/1.41  # Clauses deleted for lack of memory   : 0
% 1.21/1.41  # Backward-subsumed                    : 3
% 1.21/1.41  # Backward-rewritten                   : 21
% 1.21/1.41  # Generated clauses                    : 222267
% 1.21/1.41  # ...of the previous two non-trivial   : 82179
% 1.21/1.41  # Contextual simplify-reflections      : 6
% 1.21/1.41  # Paramodulations                      : 221753
% 1.21/1.41  # Factorizations                       : 6
% 1.21/1.41  # Equation resolutions                 : 508
% 1.21/1.41  # Propositional unsat checks           : 0
% 1.21/1.41  #    Propositional check models        : 0
% 1.21/1.41  #    Propositional check unsatisfiable : 0
% 1.21/1.41  #    Propositional clauses             : 0
% 1.21/1.41  #    Propositional clauses after purity: 0
% 1.21/1.41  #    Propositional unsat core size     : 0
% 1.21/1.41  #    Propositional preprocessing time  : 0.000
% 1.21/1.41  #    Propositional encoding time       : 0.000
% 1.21/1.41  #    Propositional solver time         : 0.000
% 1.21/1.41  #    Success case prop preproc time    : 0.000
% 1.21/1.41  #    Success case prop encoding time   : 0.000
% 1.21/1.41  #    Success case prop solver time     : 0.000
% 1.21/1.41  # Current number of processed clauses  : 705
% 1.21/1.41  #    Positive orientable unit clauses  : 374
% 1.21/1.41  #    Positive unorientable unit clauses: 11
% 1.21/1.41  #    Negative unit clauses             : 8
% 1.21/1.41  #    Non-unit-clauses                  : 312
% 1.21/1.41  # Current number of unprocessed clauses: 72231
% 1.21/1.41  # ...number of literals in the above   : 153235
% 1.21/1.41  # Current number of archived formulas  : 0
% 1.21/1.41  # Current number of archived clauses   : 25
% 1.21/1.41  # Clause-clause subsumption calls (NU) : 42249
% 1.21/1.41  # Rec. Clause-clause subsumption calls : 30948
% 1.21/1.41  # Non-unit clause-clause subsumptions  : 3953
% 1.21/1.41  # Unit Clause-clause subsumption calls : 7430
% 1.21/1.41  # Rewrite failures with RHS unbound    : 1351
% 1.21/1.41  # BW rewrite match attempts            : 14613
% 1.21/1.41  # BW rewrite match successes           : 86
% 1.21/1.41  # Condensation attempts                : 0
% 1.21/1.41  # Condensation successes               : 0
% 1.21/1.41  # Termbank termtop insertions          : 2113343
% 1.21/1.41  
% 1.21/1.41  # -------------------------------------------------
% 1.21/1.41  # User time                : 1.023 s
% 1.21/1.41  # System time              : 0.052 s
% 1.21/1.41  # Total time               : 1.075 s
% 1.21/1.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
