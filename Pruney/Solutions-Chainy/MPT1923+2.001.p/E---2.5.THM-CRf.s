%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 129 expanded)
%              Number of clauses        :   36 (  46 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  227 (1133 expanded)
%              Number of equality atoms :   14 ( 136 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v2_yellow_6(X3,X1,X2)
                & m1_yellow_6(X3,X1,X2) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X4 = X6
                                  & X5 = X7
                                  & r1_orders_2(X2,X4,X5) )
                               => r1_orders_2(X3,X6,X7) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).

fof(d9_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ( v2_yellow_6(X3,X1,X2)
              <=> ( v4_yellow_0(X3,X2)
                  & m1_yellow_0(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t61_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X1,X3,X4)
                              & r2_hidden(X5,u1_struct_0(X2)) )
                           => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v2_yellow_6(X3,X1,X2)
                  & m1_yellow_6(X3,X1,X2) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X4 = X6
                                    & X5 = X7
                                    & r1_orders_2(X2,X4,X5) )
                                 => r1_orders_2(X3,X6,X7) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_yellow_6])).

fof(c_0_9,plain,(
    ! [X22,X23,X24] :
      ( ( v4_yellow_0(X24,X23)
        | ~ v2_yellow_6(X24,X22,X23)
        | ~ m1_yellow_6(X24,X22,X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ l1_struct_0(X22) )
      & ( m1_yellow_0(X24,X23)
        | ~ v2_yellow_6(X24,X22,X23)
        | ~ m1_yellow_6(X24,X22,X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ l1_struct_0(X22) )
      & ( ~ v4_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_yellow_6(X24,X22,X23)
        | ~ m1_yellow_6(X24,X22,X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ l1_struct_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_6])])])])).

fof(c_0_10,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & v2_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk4_0 = esk6_0
    & esk5_0 = esk7_0
    & r1_orders_2(esk2_0,esk4_0,esk5_0)
    & ~ r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ l1_struct_0(X20)
      | ~ l1_waybel_0(X21,X20)
      | l1_orders_2(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ~ l1_orders_2(X14)
      | ~ v4_yellow_0(X15,X14)
      | ~ m1_yellow_0(X15,X14)
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | ~ m1_subset_1(X17,u1_struct_0(X14))
      | ~ m1_subset_1(X18,u1_struct_0(X15))
      | ~ m1_subset_1(X19,u1_struct_0(X15))
      | X18 != X16
      | X19 != X17
      | ~ r1_orders_2(X14,X16,X17)
      | ~ r2_hidden(X18,u1_struct_0(X15))
      | r1_orders_2(X15,X18,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_yellow_0])])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | ~ m1_yellow_0(X13,X12)
      | l1_orders_2(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_14,plain,
    ( m1_yellow_0(X1,X2)
    | ~ v2_yellow_6(X1,X3,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_orders_2(X2,X5,X6)
    | ~ l1_orders_2(X1)
    | ~ v4_yellow_0(X2,X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r2_hidden(X5,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_22,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_23,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ v4_yellow_0(X1,X4)
    | ~ m1_yellow_0(X1,X4)
    | ~ l1_orders_2(X4)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_27,plain,
    ( v4_yellow_0(X1,X2)
    | ~ v2_yellow_6(X1,X3,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_28,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X9,X8)
        | r2_hidden(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ r2_hidden(X9,X8)
        | m1_subset_1(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ m1_subset_1(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_xboole_0(X8) )
      & ( ~ v1_xboole_0(X9)
        | m1_subset_1(X9,X8)
        | ~ v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ v2_yellow_6(X1,X4,X5)
    | ~ m1_yellow_6(X1,X4,X5)
    | ~ l1_waybel_0(X5,X4)
    | ~ r1_orders_2(X5,X2,X3)
    | ~ l1_struct_0(X4)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X5))
    | ~ m1_subset_1(X2,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_14])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X2,X3)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_yellow_6(X1,X4,X5)
    | ~ m1_yellow_6(X1,X4,X5)
    | ~ l1_waybel_0(X5,X4)
    | ~ r1_orders_2(X5,X2,X3)
    | ~ l1_struct_0(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X5))
    | ~ m1_subset_1(X2,u1_struct_0(X5)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S024I
% 0.20/0.43  # and selection function SelectOptimalRestrPDepth2.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t21_yellow_6, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(((~(v2_struct_0(X3))&v2_yellow_6(X3,X1,X2))&m1_yellow_6(X3,X1,X2))=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X2,X4,X5))=>r1_orders_2(X3,X6,X7))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_6)).
% 0.20/0.43  fof(d9_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>(v2_yellow_6(X3,X1,X2)<=>(v4_yellow_0(X3,X2)&m1_yellow_0(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_6)).
% 0.20/0.43  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.43  fof(t61_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:((v4_yellow_0(X2,X1)&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((((X5=X3&X6=X4)&r1_orders_2(X1,X3,X4))&r2_hidden(X5,u1_struct_0(X2)))=>r1_orders_2(X2,X5,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_yellow_0)).
% 0.20/0.43  fof(dt_m1_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 0.20/0.43  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.43  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.43  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(((~(v2_struct_0(X3))&v2_yellow_6(X3,X1,X2))&m1_yellow_6(X3,X1,X2))=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X2,X4,X5))=>r1_orders_2(X3,X6,X7)))))))))), inference(assume_negation,[status(cth)],[t21_yellow_6])).
% 0.20/0.43  fof(c_0_9, plain, ![X22, X23, X24]:(((v4_yellow_0(X24,X23)|~v2_yellow_6(X24,X22,X23)|~m1_yellow_6(X24,X22,X23)|~l1_waybel_0(X23,X22)|~l1_struct_0(X22))&(m1_yellow_0(X24,X23)|~v2_yellow_6(X24,X22,X23)|~m1_yellow_6(X24,X22,X23)|~l1_waybel_0(X23,X22)|~l1_struct_0(X22)))&(~v4_yellow_0(X24,X23)|~m1_yellow_0(X24,X23)|v2_yellow_6(X24,X22,X23)|~m1_yellow_6(X24,X22,X23)|~l1_waybel_0(X23,X22)|~l1_struct_0(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_6])])])])).
% 0.20/0.43  fof(c_0_10, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_waybel_0(esk2_0,esk1_0))&(((~v2_struct_0(esk3_0)&v2_yellow_6(esk3_0,esk1_0,esk2_0))&m1_yellow_6(esk3_0,esk1_0,esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&(((esk4_0=esk6_0&esk5_0=esk7_0)&r1_orders_2(esk2_0,esk4_0,esk5_0))&~r1_orders_2(esk3_0,esk6_0,esk7_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.43  fof(c_0_11, plain, ![X20, X21]:(~l1_struct_0(X20)|(~l1_waybel_0(X21,X20)|l1_orders_2(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X14, X15, X16, X17, X18, X19]:(~l1_orders_2(X14)|(~v4_yellow_0(X15,X14)|~m1_yellow_0(X15,X14)|(~m1_subset_1(X16,u1_struct_0(X14))|(~m1_subset_1(X17,u1_struct_0(X14))|(~m1_subset_1(X18,u1_struct_0(X15))|(~m1_subset_1(X19,u1_struct_0(X15))|(X18!=X16|X19!=X17|~r1_orders_2(X14,X16,X17)|~r2_hidden(X18,u1_struct_0(X15))|r1_orders_2(X15,X18,X19)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_yellow_0])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X12, X13]:(~l1_orders_2(X12)|(~m1_yellow_0(X13,X12)|l1_orders_2(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).
% 0.20/0.43  cnf(c_0_14, plain, (m1_yellow_0(X1,X2)|~v2_yellow_6(X1,X3,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_15, negated_conjecture, (v2_yellow_6(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_16, negated_conjecture, (m1_yellow_6(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_17, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_18, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_19, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_20, plain, (r1_orders_2(X2,X5,X6)|~l1_orders_2(X1)|~v4_yellow_0(X2,X1)|~m1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X2))|X5!=X3|X6!=X4|~r1_orders_2(X1,X3,X4)|~r2_hidden(X5,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  fof(c_0_21, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.43  fof(c_0_22, plain, ![X11]:(~l1_orders_2(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.43  cnf(c_0_23, plain, (l1_orders_2(X2)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_26, plain, (r1_orders_2(X1,X2,X3)|~r1_orders_2(X4,X2,X3)|~v4_yellow_0(X1,X4)|~m1_yellow_0(X1,X4)|~l1_orders_2(X4)|~r2_hidden(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.20/0.43  cnf(c_0_27, plain, (v4_yellow_0(X1,X2)|~v2_yellow_6(X1,X3,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  fof(c_0_28, plain, ![X8, X9]:(((~m1_subset_1(X9,X8)|r2_hidden(X9,X8)|v1_xboole_0(X8))&(~r2_hidden(X9,X8)|m1_subset_1(X9,X8)|v1_xboole_0(X8)))&((~m1_subset_1(X9,X8)|v1_xboole_0(X9)|~v1_xboole_0(X8))&(~v1_xboole_0(X9)|m1_subset_1(X9,X8)|~v1_xboole_0(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_30, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_31, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.43  cnf(c_0_33, plain, (r1_orders_2(X1,X2,X3)|~v2_yellow_6(X1,X4,X5)|~m1_yellow_6(X1,X4,X5)|~l1_waybel_0(X5,X4)|~r1_orders_2(X5,X2,X3)|~l1_struct_0(X4)|~r2_hidden(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X5))|~m1_subset_1(X2,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19]), c_0_14])).
% 0.20/0.43  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (~l1_struct_0(esk3_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (~r1_orders_2(esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (esk4_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_39, plain, (r1_orders_2(X1,X2,X3)|v1_xboole_0(u1_struct_0(X1))|~v2_yellow_6(X1,X4,X5)|~m1_yellow_6(X1,X4,X5)|~l1_waybel_0(X5,X4)|~r1_orders_2(X5,X2,X3)|~l1_struct_0(X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X5))|~m1_subset_1(X2,u1_struct_0(X5))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (esk5_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (~r1_orders_2(esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk3_0,X1,X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_40])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_43, c_0_38])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_44, c_0_42])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 53
% 0.20/0.43  # Proof object clause steps            : 36
% 0.20/0.43  # Proof object formula steps           : 17
% 0.20/0.43  # Proof object conjectures             : 28
% 0.20/0.43  # Proof object clause conjectures      : 25
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 21
% 0.20/0.43  # Proof object initial formulas used   : 8
% 0.20/0.43  # Proof object generating inferences   : 9
% 0.20/0.43  # Proof object simplifying inferences  : 29
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 8
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 26
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 26
% 0.20/0.43  # Processed clauses                    : 304
% 0.20/0.43  # ...of these trivial                  : 0
% 0.20/0.43  # ...subsumed                          : 168
% 0.20/0.43  # ...remaining for further processing  : 136
% 0.20/0.43  # Other redundant clauses eliminated   : 2
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 4
% 0.20/0.43  # Generated clauses                    : 823
% 0.20/0.43  # ...of the previous two non-trivial   : 824
% 0.20/0.43  # Contextual simplify-reflections      : 3
% 0.20/0.43  # Paramodulations                      : 822
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 2
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 105
% 0.20/0.43  #    Positive orientable unit clauses  : 16
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 5
% 0.20/0.43  #    Non-unit-clauses                  : 84
% 0.20/0.43  # Current number of unprocessed clauses: 572
% 0.20/0.43  # ...number of literals in the above   : 8117
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 30
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 12192
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 11588
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 171
% 0.20/0.43  # Unit Clause-clause subsumption calls : 8
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 2
% 0.20/0.43  # BW rewrite match successes           : 2
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 21407
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.087 s
% 0.20/0.43  # System time              : 0.003 s
% 0.20/0.43  # Total time               : 0.090 s
% 0.20/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
