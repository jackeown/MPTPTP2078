%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:37 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 232 expanded)
%              Number of clauses        :   41 (  88 expanded)
%              Number of leaves         :    7 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 (1385 expanded)
%              Number of equality atoms :    8 ( 201 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
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
                              & r1_orders_2(X2,X5,X6) )
                           => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_yellow_0)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_yellow_0(X2,X1)
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
                                & r1_orders_2(X2,X5,X6) )
                             => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_yellow_0])).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk4_0
    & esk7_0 = esk5_0
    & r1_orders_2(esk3_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_orders_2(X20,X21,X22)
        | r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))
        | r1_orders_2(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),
    [final]).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_14])]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11]),
    [final]).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk4_0,esk4_0),u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]),
    [final]).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk7_0,esk4_0),u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_0,esk7_0)
    | ~ r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk7_0),u1_orders_2(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_25]),
    [final]).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

fof(c_0_35,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_36,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_14])]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_14])]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk4_0)
    | ~ l1_orders_2(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk7_0)
    | ~ l1_orders_2(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | ~ l1_orders_2(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_27]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ m1_subset_1(k4_tarski(esk4_0,esk4_0),u1_orders_2(esk2_0))
    | ~ r2_hidden(X1,u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_0,esk4_0)
    | ~ m1_subset_1(k4_tarski(esk7_0,esk4_0),u1_orders_2(esk2_0))
    | ~ r2_hidden(X1,u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk7_0)
    | ~ l1_orders_2(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_28]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_0,esk7_0)
    | ~ m1_subset_1(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk2_0))
    | ~ r2_hidden(X1,u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(esk4_0,esk7_0),u1_orders_2(esk2_0))
    | ~ r2_hidden(X1,u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30]),
    [final]).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34]),
    [final]).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_20]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.13/0.36  # and selection function PSelectMinOptimalNoXTypePred.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.016 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # No proof found!
% 0.13/0.36  # SZS status CounterSatisfiable
% 0.13/0.36  # SZS output start Saturation
% 0.13/0.36  fof(t60_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(((X5=X3&X6=X4)&r1_orders_2(X2,X5,X6))=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_yellow_0)).
% 0.13/0.36  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.13/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.36  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.36  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(((X5=X3&X6=X4)&r1_orders_2(X2,X5,X6))=>r1_orders_2(X1,X3,X4))))))))), inference(assume_negation,[status(cth)],[t60_yellow_0])).
% 0.13/0.36  fof(c_0_8, negated_conjecture, (l1_orders_2(esk2_0)&(m1_yellow_0(esk3_0,esk2_0)&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&(((esk6_0=esk4_0&esk7_0=esk5_0)&r1_orders_2(esk3_0,esk6_0,esk7_0))&~r1_orders_2(esk2_0,esk4_0,esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.36  fof(c_0_9, plain, ![X20, X21, X22]:((~r1_orders_2(X20,X21,X22)|r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|~l1_orders_2(X20))&(~r2_hidden(k4_tarski(X21,X22),u1_orders_2(X20))|r1_orders_2(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|~l1_orders_2(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, (esk7_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  cnf(c_0_12, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.36  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  fof(c_0_15, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.36  fof(c_0_16, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (esk6_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), ['final']).
% 0.13/0.36  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.36  cnf(c_0_23, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.36  cnf(c_0_24, negated_conjecture, (r1_orders_2(esk2_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_17]), c_0_14])]), ['final']).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_18, c_0_11]), ['final']).
% 0.13/0.36  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|~r2_hidden(k4_tarski(esk4_0,esk4_0),u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_21, c_0_13]), ['final']).
% 0.13/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~m1_subset_1(X1,X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23]), ['final']).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk2_0,esk7_0,esk4_0)|~r2_hidden(k4_tarski(esk7_0,esk4_0),u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_21, c_0_17]), ['final']).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk2_0,esk7_0,esk7_0)|~r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_17]), ['final']).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk7_0),u1_orders_2(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_25]), ['final']).
% 0.13/0.36  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.36  fof(c_0_35, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.36  fof(c_0_36, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.36  fof(c_0_37, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk2_0))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_13]), c_0_14])]), ['final']).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk2_0))|~r1_orders_2(esk2_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_14])]), ['final']).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk3_0))|~r1_orders_2(esk3_0,X1,esk4_0)|~l1_orders_2(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk3_0))|~r1_orders_2(esk3_0,X1,esk7_0)|~l1_orders_2(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_28]), ['final']).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk3_0,X1,esk4_0)|~l1_orders_2(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk3_0))), inference(spm,[status(thm)],[c_0_12, c_0_27]), ['final']).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|~m1_subset_1(k4_tarski(esk4_0,esk4_0),u1_orders_2(esk2_0))|~r2_hidden(X1,u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_30]), ['final']).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk2_0,esk7_0,esk4_0)|~m1_subset_1(k4_tarski(esk7_0,esk4_0),u1_orders_2(esk2_0))|~r2_hidden(X1,u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_30]), ['final']).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk3_0,X1,esk7_0)|~l1_orders_2(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk3_0))), inference(spm,[status(thm)],[c_0_12, c_0_28]), ['final']).
% 0.13/0.36  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk2_0,esk7_0,esk7_0)|~m1_subset_1(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk2_0))|~r2_hidden(X1,u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_30]), ['final']).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k4_tarski(esk4_0,esk7_0),u1_orders_2(esk2_0))|~r2_hidden(X1,u1_orders_2(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_30]), ['final']).
% 0.13/0.36  cnf(c_0_49, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_34]), ['final']).
% 0.13/0.36  cnf(c_0_50, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.36  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.36  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.13/0.36  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.13/0.36  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_38, c_0_20]), ['final']).
% 0.13/0.36  cnf(c_0_55, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.36  # SZS output end Saturation
% 0.13/0.36  # Proof object total steps             : 56
% 0.13/0.36  # Proof object clause steps            : 41
% 0.13/0.36  # Proof object formula steps           : 15
% 0.13/0.36  # Proof object conjectures             : 33
% 0.13/0.36  # Proof object clause conjectures      : 30
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 19
% 0.13/0.36  # Proof object initial formulas used   : 7
% 0.13/0.36  # Proof object generating inferences   : 18
% 0.13/0.36  # Proof object simplifying inferences  : 13
% 0.13/0.36  # Parsed axioms                        : 7
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 19
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 19
% 0.13/0.36  # Processed clauses                    : 60
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 4
% 0.13/0.36  # ...remaining for further processing  : 56
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 22
% 0.13/0.36  # ...of the previous two non-trivial   : 22
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 22
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 37
% 0.13/0.36  #    Positive orientable unit clauses  : 9
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 26
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 19
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 142
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 92
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.36  # Unit Clause-clause subsumption calls : 4
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1802
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.019 s
% 0.13/0.36  # System time              : 0.001 s
% 0.13/0.36  # Total time               : 0.020 s
% 0.13/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
