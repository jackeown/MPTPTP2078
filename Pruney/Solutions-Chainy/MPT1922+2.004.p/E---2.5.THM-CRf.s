%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 146 expanded)
%              Number of clauses        :   34 (  52 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  190 (1009 expanded)
%              Number of equality atoms :   11 ( 151 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
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
                                  & r1_orders_2(X3,X6,X7) )
                               => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
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
                                    & r1_orders_2(X3,X6,X7) )
                                 => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_6])).

fof(c_0_9,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk4_0 = esk6_0
    & esk5_0 = esk7_0
    & r1_orders_2(esk3_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_orders_2(X13,X14,X15)
        | r2_hidden(k4_tarski(X14,X15),u1_orders_2(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ l1_orders_2(X13) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),u1_orders_2(X13))
        | r1_orders_2(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ r2_hidden(X10,X9)
      | r2_hidden(X10,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ l1_waybel_0(X19,X18)
      | l1_orders_2(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( esk5_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_orders_2(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk7_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_orders_2(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_struct_0(X23)
      | ~ l1_waybel_0(X24,X23)
      | ~ m1_yellow_6(X25,X23,X24)
      | l1_waybel_0(X25,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_orders_2(X1,esk4_0,esk7_0)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(u1_orders_2(esk2_0)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_yellow_0(X17,X16)
        | ~ l1_orders_2(X17)
        | ~ l1_orders_2(X16) )
      & ( r1_tarski(u1_orders_2(X17),u1_orders_2(X16))
        | ~ m1_yellow_0(X17,X16)
        | ~ l1_orders_2(X17)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_tarski(u1_struct_0(X17),u1_struct_0(X16))
        | ~ r1_tarski(u1_orders_2(X17),u1_orders_2(X16))
        | m1_yellow_0(X17,X16)
        | ~ l1_orders_2(X17)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_33,plain,(
    ! [X20,X21,X22] :
      ( ( m1_yellow_0(X22,X21)
        | ~ m1_yellow_6(X22,X20,X21)
        | ~ l1_waybel_0(X22,X20)
        | ~ l1_waybel_0(X21,X20)
        | ~ l1_struct_0(X20) )
      & ( u1_waybel_0(X20,X22) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X22))
        | ~ m1_yellow_6(X22,X20,X21)
        | ~ l1_waybel_0(X22,X20)
        | ~ l1_waybel_0(X21,X20)
        | ~ l1_struct_0(X20) )
      & ( ~ m1_yellow_0(X22,X21)
        | u1_waybel_0(X20,X22) != k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X22))
        | m1_yellow_6(X22,X20,X21)
        | ~ l1_waybel_0(X22,X20)
        | ~ l1_waybel_0(X21,X20)
        | ~ l1_struct_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

cnf(c_0_34,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_orders_2(X1,esk4_0,esk7_0)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(esk2_0))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( l1_orders_2(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(pm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_yellow_0(X1,esk2_0)
    | ~ r1_orders_2(X1,esk4_0,esk7_0)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36,c_0_37]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_35]),c_0_18]),c_0_41]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(pm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.19/0.39  # and selection function NoSelection.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t20_yellow_6, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_yellow_6)).
% 0.19/0.39  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.19/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.39  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.19/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.39  fof(dt_m1_yellow_6, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>![X3]:(m1_yellow_6(X3,X1,X2)=>l1_waybel_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 0.19/0.39  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.19/0.39  fof(d8_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(l1_waybel_0(X3,X1)=>(m1_yellow_6(X3,X1,X2)<=>(m1_yellow_0(X3,X2)&u1_waybel_0(X1,X3)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_6)).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5)))))))))), inference(assume_negation,[status(cth)],[t20_yellow_6])).
% 0.19/0.39  fof(c_0_9, negated_conjecture, (l1_struct_0(esk1_0)&(l1_waybel_0(esk2_0,esk1_0)&(m1_yellow_6(esk3_0,esk1_0,esk2_0)&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&(((esk4_0=esk6_0&esk5_0=esk7_0)&r1_orders_2(esk3_0,esk6_0,esk7_0))&~r1_orders_2(esk2_0,esk4_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.39  fof(c_0_10, plain, ![X13, X14, X15]:((~r1_orders_2(X13,X14,X15)|r2_hidden(k4_tarski(X14,X15),u1_orders_2(X13))|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|~l1_orders_2(X13))&(~r2_hidden(k4_tarski(X14,X15),u1_orders_2(X13))|r1_orders_2(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|~l1_orders_2(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.19/0.39  fof(c_0_11, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|(~r2_hidden(X10,X9)|r2_hidden(X10,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X18, X19]:(~l1_struct_0(X18)|(~l1_waybel_0(X19,X18)|l1_orders_2(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.19/0.39  cnf(c_0_13, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (esk5_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_15, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_17, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  cnf(c_0_22, plain, (r1_orders_2(X1,X2,X3)|~l1_orders_2(X1)|~r2_hidden(k4_tarski(X2,X3),X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_orders_2(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk7_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_orders_2(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  fof(c_0_28, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.39  fof(c_0_29, plain, ![X23, X24, X25]:(~l1_struct_0(X23)|~l1_waybel_0(X24,X23)|(~m1_yellow_6(X25,X23,X24)|l1_waybel_0(X25,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (~r1_orders_2(X1,esk4_0,esk7_0)|~l1_orders_2(X1)|~m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(u1_orders_2(esk2_0)))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk4_0,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  fof(c_0_32, plain, ![X16, X17]:(((r1_tarski(u1_struct_0(X17),u1_struct_0(X16))|~m1_yellow_0(X17,X16)|~l1_orders_2(X17)|~l1_orders_2(X16))&(r1_tarski(u1_orders_2(X17),u1_orders_2(X16))|~m1_yellow_0(X17,X16)|~l1_orders_2(X17)|~l1_orders_2(X16)))&(~r1_tarski(u1_struct_0(X17),u1_struct_0(X16))|~r1_tarski(u1_orders_2(X17),u1_orders_2(X16))|m1_yellow_0(X17,X16)|~l1_orders_2(X17)|~l1_orders_2(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.19/0.39  fof(c_0_33, plain, ![X20, X21, X22]:(((m1_yellow_0(X22,X21)|~m1_yellow_6(X22,X20,X21)|~l1_waybel_0(X22,X20)|~l1_waybel_0(X21,X20)|~l1_struct_0(X20))&(u1_waybel_0(X20,X22)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X22))|~m1_yellow_6(X22,X20,X21)|~l1_waybel_0(X22,X20)|~l1_waybel_0(X21,X20)|~l1_struct_0(X20)))&(~m1_yellow_0(X22,X21)|u1_waybel_0(X20,X22)!=k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X22))|m1_yellow_6(X22,X20,X21)|~l1_waybel_0(X22,X20)|~l1_waybel_0(X21,X20)|~l1_struct_0(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).
% 0.19/0.39  cnf(c_0_34, plain, (l1_waybel_0(X3,X1)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_yellow_6(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (m1_yellow_6(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (~r1_orders_2(X1,esk4_0,esk7_0)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(X1),u1_orders_2(esk2_0))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk4_0,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.39  cnf(c_0_37, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (esk4_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (l1_waybel_0(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19])])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (l1_orders_2(X1)|~l1_waybel_0(X1,esk1_0)), inference(pm,[status(thm)],[c_0_17, c_0_19])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~m1_yellow_0(X1,esk2_0)|~r1_orders_2(X1,esk4_0,esk7_0)|~l1_orders_2(X1)|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk4_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36, c_0_37]), c_0_23])])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_35]), c_0_18]), c_0_41]), c_0_19])])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk3_0)), inference(pm,[status(thm)],[c_0_42, c_0_41])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_43, c_0_39])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 51
% 0.19/0.39  # Proof object clause steps            : 34
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 28
% 0.19/0.39  # Proof object clause conjectures      : 25
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 19
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 11
% 0.19/0.39  # Proof object simplifying inferences  : 24
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 8
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 24
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 24
% 0.19/0.39  # Processed clauses                    : 73
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 14
% 0.19/0.39  # ...remaining for further processing  : 58
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 515
% 0.19/0.39  # ...of the previous two non-trivial   : 508
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 515
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 57
% 0.19/0.39  #    Positive orientable unit clauses  : 14
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 42
% 0.19/0.39  # Current number of unprocessed clauses: 459
% 0.19/0.39  # ...number of literals in the above   : 3262
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 1
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 178
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 80
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.19/0.39  # Unit Clause-clause subsumption calls : 8
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 1
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 7761
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.038 s
% 0.19/0.39  # System time              : 0.007 s
% 0.19/0.39  # Total time               : 0.045 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
